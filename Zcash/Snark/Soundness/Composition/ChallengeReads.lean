import Zcash.Snark.Soundness.Pricing.ChallengePricing
import Zcash.Circuits.Integration.TopLevelLookups

/-!
# What each challenge exclusion reads

The semantic challenge budgets price exclusion sets stated at the run's accepted polynomial.
For a sequential prover the pricing must consume only data committed before the priced squeeze,
so this module locates each set's reads exactly: a congruence per set, over polynomial maps that
agree on the named commitment slots.

- `θ` reads only the three query-column classes (`isColumnInput`).
- Permutation `β`/`γ` add the common permutation columns (`isPermutationInput`); every read
  routes through `ResolverPermutationPairs`.
- Lookup `β`/`γ` add the lookup's own permuted-column commitments (`isLookupInput`); every read
  routes through the query feeds and the two direct permuted-column slots.

No set reads a product commitment, the vanishing pieces, the random polynomial, or any
claimed evaluation.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial

variable {shape : CircuitShape} {numProofs : ℕ} {G : Type*}

/-! ## The slot classes -/

/-- The three query-column classes: instance, advice, and fixed columns. -/
def CommitmentId.isColumnInput : CommitmentId → Prop
  | .instanceCol _ _ => True
  | .adviceCol _ _ => True
  | .fixedCol _ => True
  | _ => False

/-- The slots a resolver-backed permutation argument reads: the query columns and the common
permutation columns. -/
def CommitmentId.isPermutationInput : CommitmentId → Prop
  | .instanceCol _ _ => True
  | .adviceCol _ _ => True
  | .fixedCol _ => True
  | .permCommon _ => True
  | _ => False

/-- The slots a deployed lookup argument reads: the query columns and the lookup's two
permuted-column commitments. -/
def CommitmentId.isLookupInput : CommitmentId → Prop
  | .instanceCol _ _ => True
  | .adviceCol _ _ => True
  | .fixedCol _ => True
  | .lookupPermInput _ _ => True
  | .lookupPermTable _ _ => True
  | _ => False

/-- Query columns are permutation inputs. -/
theorem CommitmentId.isColumnInput.toPermutation {id : CommitmentId}
    (h : id.isColumnInput) : id.isPermutationInput := by
  cases id <;> simp_all [CommitmentId.isColumnInput, CommitmentId.isPermutationInput]

/-- Query columns are lookup inputs. -/
theorem CommitmentId.isColumnInput.toLookup {id : CommitmentId}
    (h : id.isColumnInput) : id.isLookupInput := by
  cases id <;> simp_all [CommitmentId.isColumnInput, CommitmentId.isLookupInput]

/-! ## The permutation layer -/

/-- Column selection reads only the three query-column classes. -/
theorem permutationColumnPolynomialOfResolver_congr
    (vk : VerifyingKey shape Fp G) {poly₁ poly₂ : CommitmentId → CPoly}
    (p : Fin numProofs)
    (h : ∀ id, id.isColumnInput → poly₁ id = poly₂ id) (cr : ColumnRef) :
    permutationColumnPolynomialOfResolver vk poly₁ p cr =
      permutationColumnPolynomialOfResolver vk poly₂ p cr := by
  unfold permutationColumnPolynomialOfResolver
  cases cr <;> simp only [ColumnRef.resolve]
  all_goals
    unfold finFn
    split
    · exact h _ trivial
    · rfl

/-- **The permutation pairs read only the permutation input slots.** -/
theorem resolverPermutationPairs_congr
    (vk : VerifyingKey shape Fp G) {poly₁ poly₂ : CommitmentId → CPoly}
    (p : Fin numProofs)
    (h : ∀ id, id.isPermutationInput → poly₁ id = poly₂ id) :
    ResolverPermutationPairs vk poly₁ p = ResolverPermutationPairs vk poly₂ p := by
  funext c
  unfold ResolverPermutationPairs permutationChunkPairsOfResolver
  refine congrArg (fun f => List.map f _) (funext fun cr => ?_)
  exact congrArg₂ Prod.mk
    (permutationColumnPolynomialOfResolver_congr vk p
      (fun id hid => h id hid.toPermutation) cr.1)
    (h _ trivial)

/-- The per-proof permutation `β` exclusion reads only the permutation input slots. -/
theorem resolverPermutationBetaBadSet_congr
    (vk : VerifyingKey shape Fp G) {poly₁ poly₂ : CommitmentId → CPoly}
    (p : Fin numProofs) (m : ℕ)
    (h : ∀ id, id.isPermutationInput → poly₁ id = poly₂ id) :
    resolverPermutationBetaBadSet vk poly₁ p m =
      resolverPermutationBetaBadSet vk poly₂ p m := by
  unfold resolverPermutationBetaBadSet ResolverPermutationCell
  rw [resolverPermutationPairs_congr vk p h]

/-- The per-proof permutation `γ` exclusion reads only the permutation input slots, and of the
challenge record only `β`. -/
theorem resolverPermutationGammaBadSet_congr
    (vk : VerifyingKey shape Fp G) {ch₁ ch₂ : Challenges shape.k Fp}
    {poly₁ poly₂ : CommitmentId → CPoly}
    (p : Fin numProofs) (m : ℕ) (hbeta : ch₁.beta = ch₂.beta)
    (h : ∀ id, id.isPermutationInput → poly₁ id = poly₂ id) :
    resolverPermutationGammaBadSet vk ch₁ poly₁ p m =
      resolverPermutationGammaBadSet vk ch₂ poly₂ p m := by
  unfold resolverPermutationGammaBadSet resolverPermutationGammaDifference
    resolverPermutationZeroFactorBadSet resolverPermutationFactorOffset
    ResolverPermutationCell
  rw [resolverPermutationPairs_congr vk p h, hbeta]

/-- **The bundle-wide permutation `β` exclusion reads only the permutation input slots.** -/
theorem allResolverPermutationBetaBadSet_congr
    (numProofs : ℕ)
    (vk : VerifyingKey shape Fp G) {poly₁ poly₂ : CommitmentId → CPoly} (m : ℕ)
    (h : ∀ id, id.isPermutationInput → poly₁ id = poly₂ id) :
    allResolverPermutationBetaBadSet numProofs vk poly₁ m =
      allResolverPermutationBetaBadSet numProofs vk poly₂ m := by
  unfold allResolverPermutationBetaBadSet
  exact Finset.biUnion_congr rfl
    (fun p _ => resolverPermutationBetaBadSet_congr vk p m h)

/-- **The bundle-wide permutation `γ` exclusion reads only the permutation input slots.** -/
theorem allResolverPermutationGammaBadSet_congr
    (numProofs : ℕ)
    (vk : VerifyingKey shape Fp G) {ch₁ ch₂ : Challenges shape.k Fp}
    {poly₁ poly₂ : CommitmentId → CPoly} (m : ℕ) (hbeta : ch₁.beta = ch₂.beta)
    (h : ∀ id, id.isPermutationInput → poly₁ id = poly₂ id) :
    allResolverPermutationGammaBadSet numProofs vk ch₁ poly₁ m =
      allResolverPermutationGammaBadSet numProofs vk ch₂ poly₂ m := by
  unfold allResolverPermutationGammaBadSet
  exact Finset.biUnion_congr rfl
    (fun p _ => resolverPermutationGammaBadSet_congr vk p m hbeta h)

/-! ## The lookup layer -/

/-- The fixed query feed reads only fixed columns. -/
theorem fixedQueryFeedOfResolver_congr
    (vk : VerifyingKey shape Fp G) {poly₁ poly₂ : CommitmentId → CPoly}
    (h : ∀ id, id.isColumnInput → poly₁ id = poly₂ id) :
    fixedQueryFeedOfResolver vk poly₁ = fixedQueryFeedOfResolver vk poly₂ := by
  unfold fixedQueryFeedOfResolver
  rw [show (fun column => poly₁ (.fixedCol column)) =
    (fun column => poly₂ (.fixedCol column)) from funext fun _ => h _ trivial]

/-- The advice query feed reads only the proof's advice columns. -/
theorem adviceQueryFeedOfResolver_congr
    (vk : VerifyingKey shape Fp G) {poly₁ poly₂ : CommitmentId → CPoly}
    (p : ℕ)
    (h : ∀ id, id.isColumnInput → poly₁ id = poly₂ id) :
    adviceQueryFeedOfResolver vk poly₁ p = adviceQueryFeedOfResolver vk poly₂ p := by
  unfold adviceQueryFeedOfResolver
  rw [show (fun column => poly₁ (.adviceCol p column)) =
    (fun column => poly₂ (.adviceCol p column)) from funext fun _ => h _ trivial]

/-- The instance query feed reads only the proof's instance columns. -/
theorem instanceQueryFeedOfResolver_congr
    (vk : VerifyingKey shape Fp G) {poly₁ poly₂ : CommitmentId → CPoly}
    (p : ℕ)
    (h : ∀ id, id.isColumnInput → poly₁ id = poly₂ id) :
    instanceQueryFeedOfResolver vk poly₁ p = instanceQueryFeedOfResolver vk poly₂ p := by
  unfold instanceQueryFeedOfResolver
  rw [show (fun column => poly₁ (.instanceCol p column)) =
    (fun column => poly₂ (.instanceCol p column)) from funext fun _ => h _ trivial]

/-- The compressed input polynomial reads only the query columns. -/
theorem lookupInputPolyOfResolver_congr
    {k : ℕ} (vk : VerifyingKey shape Fp G) {ch₁ ch₂ : Challenges k Fp}
    {poly₁ poly₂ : CommitmentId → CPoly}
    (p : ℕ) (l : Fin shape.numLookups) (htheta : ch₁.theta = ch₂.theta)
    (h : ∀ id, id.isColumnInput → poly₁ id = poly₂ id) :
    lookupInputPolyOfResolver vk ch₁ poly₁ p l =
      lookupInputPolyOfResolver vk ch₂ poly₂ p l := by
  unfold lookupInputPolyOfResolver
  rw [fixedQueryFeedOfResolver_congr vk h, adviceQueryFeedOfResolver_congr vk p h,
    instanceQueryFeedOfResolver_congr vk p h, htheta]

/-- The compressed table polynomial reads only the query columns. -/
theorem lookupTablePolyOfResolver_congr
    {k : ℕ} (vk : VerifyingKey shape Fp G) {ch₁ ch₂ : Challenges k Fp}
    {poly₁ poly₂ : CommitmentId → CPoly}
    (p : ℕ) (l : Fin shape.numLookups) (htheta : ch₁.theta = ch₂.theta)
    (h : ∀ id, id.isColumnInput → poly₁ id = poly₂ id) :
    lookupTablePolyOfResolver vk ch₁ poly₁ p l =
      lookupTablePolyOfResolver vk ch₂ poly₂ p l := by
  unfold lookupTablePolyOfResolver
  rw [fixedQueryFeedOfResolver_congr vk h, adviceQueryFeedOfResolver_congr vk p h,
    instanceQueryFeedOfResolver_congr vk p h, htheta]

/-- **The lookup product difference reads only the lookup input slots.** -/
theorem resolverLookupProductDifference_congr
    {k : ℕ} (vk : VerifyingKey shape Fp G) {ch₁ ch₂ : Challenges k Fp}
    {poly₁ poly₂ : CommitmentId → CPoly}
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ)
    (htheta : ch₁.theta = ch₂.theta)
    (h : ∀ id, id.isLookupInput → poly₁ id = poly₂ id) :
    resolverLookupProductDifference vk ch₁ poly₁ p l u =
      resolverLookupProductDifference vk ch₂ poly₂ p l u := by
  unfold resolverLookupProductDifference
  rw [h (.lookupPermInput p l) trivial, h (.lookupPermTable p l) trivial,
    lookupInputPolyOfResolver_congr vk p l htheta (fun id hid => h id hid.toLookup),
    lookupTablePolyOfResolver_congr vk p l htheta (fun id hid => h id hid.toLookup)]

/-- The same reading for the computable coefficient family. -/
theorem resolverLookupProductDifferenceCoeff_congr
    {k : ℕ} (vk : VerifyingKey shape Fp G) {ch₁ ch₂ : Challenges k Fp}
    {poly₁ poly₂ : CommitmentId → CPoly}
    (p : ℕ) (l : Fin shape.numLookups) (u j : ℕ)
    (htheta : ch₁.theta = ch₂.theta)
    (h : ∀ id, id.isLookupInput → poly₁ id = poly₂ id) :
    resolverLookupProductDifferenceCoeff vk ch₁ poly₁ p l u j =
      resolverLookupProductDifferenceCoeff vk ch₂ poly₂ p l u j := by
  unfold resolverLookupProductDifferenceCoeff
  rw [h (.lookupPermInput p l) trivial, h (.lookupPermTable p l) trivial,
    lookupInputPolyOfResolver_congr vk p l htheta (fun id hid => h id hid.toLookup),
    lookupTablePolyOfResolver_congr vk p l htheta (fun id hid => h id hid.toLookup)]

/-- The same reading for the difference after `β` is fixed. -/
theorem resolverLookupProductDifferenceGamma_congr
    {k : ℕ} (vk : VerifyingKey shape Fp G) {ch₁ ch₂ : Challenges k Fp}
    {poly₁ poly₂ : CommitmentId → CPoly}
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ)
    (htheta : ch₁.theta = ch₂.theta) (hbeta : ch₁.beta = ch₂.beta)
    (h : ∀ id, id.isLookupInput → poly₁ id = poly₂ id) :
    resolverLookupProductDifferenceGamma vk ch₁ poly₁ p l u =
      resolverLookupProductDifferenceGamma vk ch₂ poly₂ p l u := by
  unfold resolverLookupProductDifferenceGamma
  rw [h (.lookupPermInput p l) trivial, h (.lookupPermTable p l) trivial,
    lookupInputPolyOfResolver_congr vk p l htheta (fun id hid => h id hid.toLookup),
    lookupTablePolyOfResolver_congr vk p l htheta (fun id hid => h id hid.toLookup), hbeta]

/-- The per-lookup `β` exclusion reads only the lookup input slots, and of the challenge
record only `θ`. -/
theorem resolverLookupBetaBadSet_congr
    {k : ℕ} (vk : VerifyingKey shape Fp G) {ch₁ ch₂ : Challenges k Fp}
    {poly₁ poly₂ : CommitmentId → CPoly}
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ)
    (htheta : ch₁.theta = ch₂.theta)
    (h : ∀ id, id.isLookupInput → poly₁ id = poly₂ id) :
    resolverLookupBetaBadSet vk ch₁ poly₁ p l u =
      resolverLookupBetaBadSet vk ch₂ poly₂ p l u := by
  unfold resolverLookupBetaBadSet
  rw [show (fun j => szBadSet (resolverLookupProductDifferenceCoeff vk ch₁ poly₁ p l u j))
      = fun j => szBadSet (resolverLookupProductDifferenceCoeff vk ch₂ poly₂ p l u j) from
        funext fun j => by
          rw [resolverLookupProductDifferenceCoeff_congr vk p l u j htheta h],
    lookupInputPolyOfResolver_congr vk p l htheta (fun id hid => h id hid.toLookup)]

/-- The per-lookup `γ` exclusion reads only the lookup input slots, and of the challenge
record only `θ` and `β`. -/
theorem resolverLookupGammaBadSet_congr
    {k : ℕ} (vk : VerifyingKey shape Fp G) {ch₁ ch₂ : Challenges k Fp}
    {poly₁ poly₂ : CommitmentId → CPoly}
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ)
    (htheta : ch₁.theta = ch₂.theta) (hbeta : ch₁.beta = ch₂.beta)
    (h : ∀ id, id.isLookupInput → poly₁ id = poly₂ id) :
    resolverLookupGammaBadSet vk ch₁ poly₁ p l u =
      resolverLookupGammaBadSet vk ch₂ poly₂ p l u := by
  unfold resolverLookupGammaBadSet
  rw [resolverLookupProductDifferenceGamma_congr vk p l u htheta hbeta h,
    lookupTablePolyOfResolver_congr vk p l htheta (fun id hid => h id hid.toLookup)]

/-- **The bundle-wide lookup `β` exclusion reads only the lookup input slots.** -/
theorem allResolverLookupBetaBadSet_congr
    {k : ℕ} (numProofs : ℕ) (vk : VerifyingKey shape Fp G)
    {ch₁ ch₂ : Challenges k Fp}
    {poly₁ poly₂ : CommitmentId → CPoly} (u : ℕ)
    (htheta : ch₁.theta = ch₂.theta)
    (h : ∀ id, id.isLookupInput → poly₁ id = poly₂ id) :
    allResolverLookupBetaBadSet numProofs vk ch₁ poly₁ u =
      allResolverLookupBetaBadSet numProofs vk ch₂ poly₂ u := by
  unfold allResolverLookupBetaBadSet
  exact Finset.biUnion_congr rfl
    (fun q _ => resolverLookupBetaBadSet_congr vk q.1 q.2 u htheta h)

/-- **The bundle-wide lookup `γ` exclusion reads only the lookup input slots.** -/
theorem allResolverLookupGammaBadSet_congr
    {k : ℕ} (numProofs : ℕ) (vk : VerifyingKey shape Fp G)
    {ch₁ ch₂ : Challenges k Fp}
    {poly₁ poly₂ : CommitmentId → CPoly} (u : ℕ)
    (htheta : ch₁.theta = ch₂.theta) (hbeta : ch₁.beta = ch₂.beta)
    (h : ∀ id, id.isLookupInput → poly₁ id = poly₂ id) :
    allResolverLookupGammaBadSet numProofs vk ch₁ poly₁ u =
      allResolverLookupGammaBadSet numProofs vk ch₂ poly₂ u := by
  unfold allResolverLookupGammaBadSet
  exact Finset.biUnion_congr rfl
    (fun q _ => resolverLookupGammaBadSet_congr vk q.1 q.2 u htheta hbeta h)

/-! ## The `θ` layer -/

/-- The row environment reads only the proof's query columns. -/
theorem resolverEnvironment_congr
    {shape : CircuitShape}
    (vk : VerifyingKey shape Fp G) {poly₁ poly₂ : CommitmentId → CPoly}
    (p : ℕ) (usableRows : ℕ)
    (h : ∀ id, id.isColumnInput → poly₁ id = poly₂ id) :
    resolverEnvironment vk poly₁ p usableRows = resolverEnvironment vk poly₂ p usableRows := by
  unfold resolverEnvironment
  rw [show (fun column => poly₁ (CommitmentId.fixedCol column)) =
    (fun column => poly₂ (CommitmentId.fixedCol column)) from funext fun _ => h _ trivial]
  rw [show (fun column => poly₁ (CommitmentId.adviceCol p column)) =
    (fun column => poly₂ (CommitmentId.adviceCol p column)) from funext fun _ => h _ trivial]
  rw [show (fun column => poly₁ (CommitmentId.instanceCol p column)) =
    (fun column => poly₂ (CommitmentId.instanceCol p column)) from funext fun _ => h _ trivial]

/-- **The `θ` budget is a length count.**  Row count times input arity per activation — the
polynomial map and the URS never enter, so the per-state `θ` epsilon is one number per
circuit. -/
theorem TopLevelLookup.thetaBudget_eq
    {G' : Type} [AddCommGroup G'] [Inhabited G']
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    [Halo2.TopLevelShape top]
    (pp : ProofParams) (urs : URS G')
    (poly : CommitmentId → CPoly) :
    TopLevelLookup.thetaBudget top pp urs poly =
      ∑ index : TopLevelLookup.ActivationIndex top pp,
        top.usableRowsAt top.domainExponent *
          ((operationEnabledLookups top.operations 0).get index.2).argument.inputs.length := by
  unfold TopLevelLookup.thetaBudget
  refine Finset.sum_congr rfl fun index _ => ?_
  exact congrArg (top.usableRowsAt top.domainExponent * ·) (List.length_map _)

/-- **The top-level `θ` exclusion reads only the query columns.** -/
theorem TopLevelLookup.thetaBadSet_congr
    {G' : Type} [AddCommGroup G'] [Inhabited G']
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : Halo2.TopLevelCircuit Fp Config PublicInput)
    [Halo2.TopLevelShape top]
    (pp : ProofParams) (urs : URS G')
    {poly₁ poly₂ : CommitmentId → CPoly}
    (h : ∀ id, id.isColumnInput → poly₁ id = poly₂ id) :
    TopLevelLookup.thetaBadSet top pp urs poly₁ =
      TopLevelLookup.thetaBadSet top pp urs poly₂ := by
  unfold TopLevelLookup.thetaBadSet
  exact Finset.biUnion_congr rfl fun index _ =>
    congrArg (fun env => EnabledLookup.thetaBadSet top.placement env
        ((operationEnabledLookups top.operations 0).get index.2))
      (resolverEnvironment_congr (top.toVerifierKey urs) index.1
        (top.usableRowsAt top.domainExponent) h)

end Zcash.Snark
