import Zcash.Snark.Keygen.Pipeline
import Zcash.Snark.Soundness.Canonical.ConstraintModel
import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Circuits.Integration.TopLevelAssignment

/-!
# Circuit-derived canonical constraint models

This module closes the domain-law boundary between a Clean top-level circuit and
ironwood's verifier-native canonical constraint model. Arbitrary verification
keys still require an explicit proof that their blinding rows fit the domain;
a key derived from `TopLevelCircuit` carries that fact by construction.
-/

namespace Halo2.TopLevelCircuit

open Zcash.Snark
open Zcash
open Zcash.Snark.Keygen
open Halo2 CompPoly.CPolynomial

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/--
The canonical resolver model for a circuit's own verification key.

Unlike the arbitrary-key constructor, this interface has no domain-law
argument: domain fitting follows from the `TopLevelCircuit` compilation.
-/
def constraintModel {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    ConstraintPolyModel pp.numProofs :=
  let vk := top.toVerifierKey urs
  let selectors := canonicalLagrangePolynomials vk.omega
    (top.toVerifierKey_blindingFactors_lt_n urs)
  constraintModelOfResolver
    (numProofs := pp.numProofs)
    (k := k)
    vk ch poly
    (permutationSetsOfResolver
      (shape := top.shape.withProofParams pp) vk poly)
    (permutationChunksOfResolver
      (shape := top.shape.withProofParams pp) vk poly)
    selectors.1 selectors.2.1 selectors.2.2

/-- The top-level canonical model exposes the resolver construction used by its
verification key without requiring consumers to unfold circuit compilation. -/
theorem constraintModel_eq_constraintModelOfResolver
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    let selectors := canonicalLagrangePolynomials top.omega
      (top.toVerifierKey_blindingFactors_lt_n urs)
    top.constraintModel pp urs ch poly =
      constraintModelOfResolver
        (numProofs := pp.numProofs)
        (k := k)
        (top.toVerifierKey urs) ch poly
        (permutationSetsOfResolver
          (shape := top.shape.withProofParams pp)
          (top.toVerifierKey urs) poly)
        (permutationChunksOfResolver
          (shape := top.shape.withProofParams pp)
          (top.toVerifierKey urs) poly)
        selectors.1 selectors.2.1 selectors.2.2 := by
  unfold constraintModel
  simp only [top.toVerifierKey_omega, constraintModelOfResolver]

/-- For challenges indexed by the circuit domain, the top-level model is the
canonical model of its derived verification key. -/
theorem constraintModel_eq_toVerifierKey_constraintModel
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges top.domainExponent Fp) (poly : CommitmentId → CPoly) :
    top.constraintModel pp urs ch poly =
      (top.toVerifierKey urs).constraintModel
        (numProofs := pp.numProofs) ch poly
        (top.toVerifierKey_blindingFactors_lt_n urs) := by
  simp only [TopLevelCircuit.constraintModel,
    VerifyingKey.constraintModel,
    top.toVerifierKey_omega]
  congr 1

@[simp] theorem constraintModel_l0
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    (top.constraintModel pp urs ch poly).l0 =
      (canonicalLagrangePolynomials top.omega
        (top.toVerifierKey_blindingFactors_lt_n urs)).1 := by
  unfold constraintModel
  simp only [top.toVerifierKey_omega, constraintModelOfResolver]

@[simp] theorem constraintModel_lLast
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    (top.constraintModel pp urs ch poly).lLast =
      (canonicalLagrangePolynomials top.omega
        (top.toVerifierKey_blindingFactors_lt_n urs)).2.1 := by
  unfold constraintModel
  simp only [top.toVerifierKey_omega, constraintModelOfResolver]

@[simp] theorem constraintModel_lBlind
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    (top.constraintModel pp urs ch poly).lBlind =
      (canonicalLagrangePolynomials top.omega
        (top.toVerifierKey_blindingFactors_lt_n urs)).2.2 := by
  unfold constraintModel
  simp only [top.toVerifierKey_omega, constraintModelOfResolver]

/-- The resolver presentation can use the top-level model's own selector
projections. This is the canonical form for consumers that pair satisfaction
with a domain law stated over those same projections. -/
theorem constraintModel_eq_constraintModelOfResolver_projections
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    top.constraintModel pp urs ch poly =
      constraintModelOfResolver
        (numProofs := pp.numProofs)
        (k := k)
        (top.toVerifierKey urs) ch poly
        (permutationSetsOfResolver
          (shape := top.shape.withProofParams pp)
          (top.toVerifierKey urs) poly)
        (permutationChunksOfResolver
          (shape := top.shape.withProofParams pp)
          (top.toVerifierKey urs) poly)
        (top.constraintModel pp urs ch poly).l0
        (top.constraintModel pp urs ch poly).lLast
        (top.constraintModel pp urs ch poly).lBlind := by
  rw [top.constraintModel_eq_constraintModelOfResolver]
  simp only [constraintModelOfResolver]

/-- Resolver pairing preserves the compiler-prescribed width of every
circuit-derived permutation chunk. -/
theorem resolverPermutationPairs_length
    (top : TopLevelCircuit Fp Config PublicInput)
    {numProofs : ℕ} (urs : URS G) (poly : CommitmentId → CPoly)
    (proofIndex : Fin numProofs)
    (chunk : Fin top.permutationSetCount) :
    (ResolverPermutationPairs
        (top.toVerifierKey urs) poly proofIndex chunk).length =
      min top.chunkLen
        (top.permutationColumnCount - (chunk : ℕ) * top.chunkLen) := by
  simp only [ResolverPermutationPairs,
    permutationChunkPairsOfResolver, List.length_map]
  apply top.toVerifierKey_permutationChunks_getD_length
  rw [top.toVerifierKey_permutationChunks_length]
  exact chunk.isLt

/-- The canonical model of a circuit-derived key satisfies the complete
permutation-domain interface. Only support for the circuit's evaluation-domain
exponent is external; chunking and blinding bounds follow from compilation. -/
theorem resolverPermutationDomain
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges top.domainExponent Fp)
    (poly : CommitmentId → CPoly)
    (hdomainExponent : top.domainExponent < 33) :
    ResolverPermutationDomain (top.toVerifierKey urs)
      (top.constraintModel pp urs ch poly).l0
      (top.constraintModel pp urs ch poly).lLast
      (top.constraintModel pp urs ch poly).lBlind
      top.n (top.usableRowsAt top.domainExponent) := by
  simpa only [top.toVerifierKey_n,
    top.toVerifierKey_blindingFactors,
    top.usableRowsAt_domainExponent] using
    ResolverPermutationDomain.ofCanonicalConstraintModel
      (top.toVerifierKey urs) ch poly
      (top.toVerifierKey_blindingFactors_lt_n urs)
      (TopLevelAssignment.toVerifierKey_domainRowsInjective
        urs hdomainExponent)
      (TopLevelAssignment.toVerifierKey_domainRoot
        urs hdomainExponent)
      (top.toVerifierKey_permutationChunks_length urs)

/-- Assemble a semantic permutation cycle from a circuit-derived keygen
permutation while keeping circuit-owned domain and chunk constants in their
canonical spelling. -/
def resolverPermutationCycleOfKeygenColumns
    (top : TopLevelCircuit Fp Config PublicInput)
    {numProofs : ℕ} (urs : URS G)
    (poly : CommitmentId → CPoly) (p : Fin numProofs)
    {activeRows : ℕ} (hactive : activeRows ≤ top.n)
    (fullSigma : Equiv.Perm
      (ResolverPermutationCell (top.toVerifierKey urs) poly p top.n))
    (sigma : Equiv.Perm
      (ResolverPermutationCell (top.toVerifierKey urs) poly p activeRows))
    (hdomainExponent : top.domainExponent < 33)
    (hcolumns : ∀
      (chunk : Fin top.permutationSetCount)
      (column : Fin
        (ResolverPermutationPairs
          (top.toVerifierKey urs) poly p chunk).length),
      (ResolverPermutationPairs
          (top.toVerifierKey urs) poly p chunk)[column].2 =
        keygenSigmaColumn top.omega Zcash.Arithmetic.deltaFp
          top.chunkLen fullSigma chunk column)
    (hrestrict : ∀ c :
        ResolverPermutationCell
          (top.toVerifierKey urs) poly p activeRows,
      widenPermutationChunkCell hactive (sigma c) =
        fullSigma (widenPermutationChunkCell hactive c))
    (hnames : Function.Injective fun c :
        ResolverPermutationCell
          (top.toVerifierKey urs) poly p activeRows =>
      chunkRowName top.omega Zcash.Arithmetic.deltaFp
        top.chunkLen c.1 c.2.1 c.2.2) :
    ResolverPermutationCycle
      (top.toVerifierKey urs) poly p activeRows := by
  have hcolumns' : ∀
      (chunk : Fin top.permutationSetCount)
      (column : Fin
        (ResolverPermutationPairs
          (top.toVerifierKey urs) poly p chunk).length),
      (ResolverPermutationPairs
          (top.toVerifierKey urs) poly p chunk)[column].2 =
        keygenSigmaColumn (top.toVerifierKey urs).omega
          (top.toVerifierKey urs).delta
          (top.toVerifierKey urs).chunkLen fullSigma chunk column := by
    simpa only [top.toVerifierKey_omega, top.toVerifierKey_delta,
      top.toVerifierKey_chunkLen] using hcolumns
  have hnames' : Function.Injective fun c :
      ResolverPermutationCell
        (top.toVerifierKey urs) poly p activeRows =>
    chunkRowName (top.toVerifierKey urs).omega
      (top.toVerifierKey urs).delta
      (top.toVerifierKey urs).chunkLen c.1 c.2.1 c.2.2 := by
    simpa only [top.toVerifierKey_omega, top.toVerifierKey_delta,
      top.toVerifierKey_chunkLen] using hnames
  have hrows : Function.Injective fun i : Fin top.n =>
      (top.toVerifierKey urs).omega ^ (i : ℕ) := by
    simpa only [top.toVerifierKey_omega] using
      TopLevelAssignment.domainRowsInjective
        (top := top) hdomainExponent
  exact ResolverPermutationCycle.ofKeygenColumns
    (top.toVerifierKey urs) poly p hactive fullSigma sigma
      hrows hcolumns' hrestrict hnames'

/-- The last usable row of a circuit-derived verifier domain is the verifier's
canonical negative blinding rotation. -/
theorem toVerifierKey_lastUsableRowRotation
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G)
    (hdomainExponent : top.domainExponent < 33) :
    (top.toVerifierKey urs).omega ^
        ((top.toVerifierKey urs).n -
          (top.toVerifierKey urs).blindingFactors - 1) =
      (top.toVerifierKey urs).omega ^
        (-(((top.toVerifierKey urs).blindingFactors : ℤ) + 1)) := by
  rw [show (top.toVerifierKey urs).n -
      (top.toVerifierKey urs).blindingFactors - 1 =
        (top.toVerifierKey urs).n -
          ((top.toVerifierKey urs).blindingFactors + 1) by omega]
  exact domain_pow_sub_eq_zpow_neg
    (by
      have hblinding := top.toVerifierKey_blindingFactors_lt_n urs
      omega)
    (TopLevelAssignment.toVerifierKey_domainRoot
      urs hdomainExponent)

end Halo2.TopLevelCircuit
