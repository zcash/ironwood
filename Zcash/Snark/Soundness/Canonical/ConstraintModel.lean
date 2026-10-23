import Zcash.Snark.Soundness.Canonical.DomainSelectors
import Zcash.Snark.Soundness.Canonical.PermutationSemantics
import Zcash.Snark.Soundness.Canonical.LookupSemantics
import Zcash.Snark.Verifier.FieldSupport

/-!
# Canonical resolver-backed constraint models

The deployed vanishing check computes its Lagrange selectors from the evaluation
domain at every transcript challenge. The polynomial soundness argument must use
one fixed selector triple across those challenges. This module installs the
canonical fixed triple directly into the generic commitment-ID resolver model.

No circuit or concrete verifying key is selected here. Field support and key
lawfulness identify evaluation of the fixed polynomials with the verifier's
deployed `lagrangeBasis` computation.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial

set_option maxHeartbeats 20000

namespace VerifyingKey

/--
The full commitment-ID resolver model with its selector polynomials determined
by the verification key's domain and blinding count.
-/
def constraintModel
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    ConstraintPolyModel numProofs :=
  let selectors :=
    canonicalLagrangePolynomials vk.omega hblinding
  constraintModelOfResolver (numProofs := numProofs) vk ch poly
    (permutationSetsOfResolver (numProofs := numProofs) vk poly)
    (permutationChunksOfResolver (numProofs := numProofs) vk poly)
    selectors.1 selectors.2.1 selectors.2.2

@[simp] theorem constraintModel_fixedCols
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).fixedCols =
      fixedQueryFeedOfResolver vk poly :=
  rfl

@[simp] theorem constraintModel_adviceCols
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).adviceCols =
      fun proofIndex : Fin numProofs =>
        adviceQueryFeedOfResolver vk poly proofIndex :=
  rfl

@[simp] theorem constraintModel_instanceCols
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).instanceCols =
      fun proofIndex : Fin numProofs =>
        instanceQueryFeedOfResolver vk poly proofIndex :=
  rfl

@[simp] theorem constraintModel_gates
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).gates = vk.gates :=
  rfl

@[simp] theorem constraintModel_sets
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n)
    (proofIndex : Fin numProofs) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).sets proofIndex =
      permutationSetsOfResolver vk poly proofIndex :=
  rfl

@[simp] theorem constraintModel_chunks
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n)
    (proofIndex : Fin numProofs) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).chunks proofIndex =
      permutationChunksOfResolver vk poly proofIndex :=
  rfl

@[simp] theorem constraintModel_lookups
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n)
    (proofIndex : Fin numProofs) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).lookups proofIndex =
      lookupEntriesOfResolver vk poly proofIndex :=
  rfl

/--
Expose the resolver-backed construction without forcing downstream proofs to
unfold the computable polynomial implementation.
-/
theorem constraintModel_eq_constraintModelOfResolver
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    vk.constraintModel (numProofs := numProofs) ch poly hblinding =
      constraintModelOfResolver (numProofs := numProofs) vk ch poly
        (permutationSetsOfResolver (numProofs := numProofs) vk poly)
        (permutationChunksOfResolver (numProofs := numProofs) vk poly)
        (vk.constraintModel (numProofs := numProofs) ch poly hblinding).l0
        (vk.constraintModel (numProofs := numProofs) ch poly hblinding).lLast
        (vk.constraintModel (numProofs := numProofs) ch poly hblinding).lBlind := by
  rfl

@[simp] theorem constraintModel_l0
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).l0 =
      (canonicalLagrangePolynomials vk.omega hblinding).1 :=
  rfl

@[simp] theorem constraintModel_lLast
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).lLast =
      (canonicalLagrangePolynomials vk.omega hblinding).2.1 :=
  rfl

@[simp] theorem constraintModel_lBlind
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).lBlind =
      (canonicalLagrangePolynomials vk.omega hblinding).2.2 :=
  rfl

/--
The canonical resolver model's fixed selector polynomials evaluate to the
verifier's exact deployed selector triple at every challenge outside the
evaluation domain.
-/
theorem constraintModel_selectorEvaluations
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    [Zcash.Arithmetic.FieldDomainParams Fp]
    (vk : VerifyingKey shape Fp G) [FieldSupport vk] (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n)
    (hxDomain : ch.x ^ vk.n ≠ 1) :
    let model := vk.constraintModel (numProofs := numProofs) ch poly hblinding
    (model.l0.eval ch.x, model.lLast.eval ch.x,
      model.lBlind.eval ch.x) =
        lagrangeBasis vk.omega vk.n vk.blindingFactors
          (ch.x ^ vk.n) ch.x := by
  simpa [VerifyingKey.constraintModel] using
    canonicalLagrangePolynomials_eval
      hblinding vk.domainRowsInjective vk.omega_pow_n vk.n_cast_ne_zero hxDomain

end VerifyingKey

/--
The canonical model satisfies the permutation-domain interface. Key lawfulness
and field support supply its chunk, selector and last-rotation properties.
-/
theorem ResolverPermutationDomain.ofCanonicalConstraintModel
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    [Zcash.Arithmetic.FieldDomainParams Fp]
    (vk : VerifyingKey shape Fp G) [VerifyingKey.FieldSupport vk]
    [VerifyingKey.WellFormed vk] (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    let model := vk.constraintModel (numProofs := numProofs) ch poly hblinding
    ResolverPermutationDomain vk model.l0 model.lLast model.lBlind
      vk.n (vk.n - vk.blindingFactors - 1) := by
  have hn : 0 < vk.n := Nat.zero_lt_of_lt hblinding
  have hm : vk.n - vk.blindingFactors - 1 < vk.n := by
    omega
  have hlastRotation :
      vk.omega ^ (vk.n - vk.blindingFactors - 1) =
        vk.omega ^ (-((vk.blindingFactors : ℤ) + 1)) := by
    rw [show vk.n - vk.blindingFactors - 1 =
      vk.n - (vk.blindingFactors + 1) by omega]
    exact domain_pow_sub_eq_zpow_neg
      (t := vk.blindingFactors + 1) (by omega) vk.omega_pow_n
  simpa [VerifyingKey.constraintModel,
    canonicalLagrangePolynomials, lastUsableDomainRow] using
      ResolverPermutationDomain.ofCanonicalSelectors vk hn hm vk.domainRowsInjective
        (VerifyingKey.WellFormed.permutationChunks_length (vk := vk))
        hlastRotation vk.omega_pow_n

/--
The canonical row-selector polynomials satisfy the lookup-domain interface
through every row strictly before its final usable row.
-/
theorem ResolverLookupDomain.ofCanonicalPolynomials
    {shape : CircuitShape} {G : Type*}
    [Zcash.Arithmetic.FieldDomainParams Fp]
    (vk : VerifyingKey shape Fp G) [VerifyingKey.FieldSupport vk]
    [VerifyingKey.WellFormed vk] :
    let selectors := canonicalLagrangePolynomials vk.omega
      vk.blindingFactors_lt_n
    ResolverLookupDomain vk selectors.1 selectors.2.1 selectors.2.2
      vk.n (vk.n - vk.blindingFactors - 2) := by
  let hblinding : vk.blindingFactors < vk.n :=
    vk.blindingFactors_lt_n
  have husable := VerifyingKey.WellFormed.blindingFactors_add_one_lt_n (vk := vk)
  have hlast :
      vk.n - vk.blindingFactors - 2 + 1 < vk.n := by
    omega
  have hlastRow :
      (⟨vk.n - vk.blindingFactors - 2 + 1, hlast⟩ : Fin vk.n) =
        lastUsableDomainRow hblinding := by
    apply Fin.ext
    simp only [lastUsableDomainRow]
    omega
  have hdomain :=
    ResolverLookupDomain.ofCanonicalSelectors vk hlast vk.domainRowsInjective
      vk.omega_ne_zero vk.omega_pow_n
  rw [hlastRow] at hdomain
  simpa [hblinding, canonicalLagrangePolynomials] using hdomain

end Zcash.Snark
