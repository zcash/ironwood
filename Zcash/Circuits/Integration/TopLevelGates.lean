import Zcash.Arithmetic.Domain
import Zcash.Circuits.Integration.ResolverGates
import Zcash.Circuits.Integration.ResolverQueryEnvironment
import Zcash.Circuits.Integration.SelectorCoherence
import Zcash.Circuits.Integration.TopLevelConstraintModel

/-!
# Generic top-level gate bridge

This module packages the static facts needed to use a closed formal circuit's own
derived verifying key. The package is circuit-independent and cannot be paired with
an arbitrary key: every verifier-side object below uses
`TopLevelCircuit.toVerifierKey`.

Given that static package and realization of the circuit-derived packed selector
rows by the decoded fixed polynomials, every enabled circuit gate receives the
polynomial witness consumed by the generic constraint-satisfaction split.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (omegaOf scalarFieldOrder)

open Halo2 CompPoly.CPolynomial Keygen

/-- Numerical bounds required by the polynomial bridge. Gate and lookup registration
and selector allocation follow generically from the top-level circuit's packaged
lawfulness; no placement, operation stream, selector map, or pinned constraint system
is supplied by the caller. -/
structure TopLevelConstraintBounds
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) : Prop where
  domainExponent_lt : top.domainExponent < 33
  selectorDegree :
    csDegree top.constraintSystem < scalarFieldOrder

namespace TopLevelConstraintBounds

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : ProofParams} {urs : URS G}

/--
The final pinned query state interprets the resolver feeds, and restricts to the
intermediate gate-erasure state because lookup erasure only appends query entries.
-/
theorem resolverInterpretsGates
    (coherence : TopLevelConstraintBounds top)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (usableRows row : ℕ) :
    Interprets
      top.gateQueryState
      (fun query =>
        (fixedQueryFeedOfResolver
          (top.toVerifierKey urs) poly query).eval
          (top.omega ^ row))
      (fun query =>
        (adviceQueryFeedOfResolver
          (top.toVerifierKey urs) poly proofIndex query).eval
          (top.omega ^ row))
      (fun query =>
        (instanceQueryFeedOfResolver
          (top.toVerifierKey urs) poly proofIndex query).eval
          (top.omega ^ row))
      (Query.eval
        (resolverEnvironment
          (top.toVerifierKey urs) poly proofIndex usableRows)
        (fun _ => 0) row) := by
  have homega : top.omega ≠ 0 := by
    have hk : top.domainExponent ≤ 32 :=
      Nat.le_of_lt_succ (by simpa using coherence.domainExponent_lt)
    exact top.omega_ne_zero hk
  have hfinal := resolverQueryFeeds_interpret
    (top.toVerifierKey urs) poly proofIndex usableRows
    (fun _ => 0) row
    (by simpa only [top.toVerifierKey_omega] using homega)
    (pinnedQueryState top.pinnedCS)
    (by
      simp only [top.toVerifierKey_adviceQueryLayout,
        TopLevelCircuit.adviceQueryLayout, pinnedQueryState])
    (by
      simp only [top.toVerifierKey_fixedQueryLayout,
        TopLevelCircuit.fixedQueryLayout, pinnedQueryState])
    (by
      simp only [top.toVerifierKey_instanceQueryLayout,
        TopLevelCircuit.instanceQueryLayout, pinnedQueryState])
    (top.toVerifierKey_adviceQueryCount urs)
    (top.toVerifierKey_fixedQueryCount urs)
    (top.toVerifierKey_instanceQueryCount urs)
  rw [top.pinnedQueryState_eq_gateQueryState] at hfinal
  simpa only [top.toVerifierKey_omega] using hfinal

/-- The circuit-derived selector map has the roots required by gate scaling. -/
theorem selectorRootsWellFormed
    (coherence : TopLevelConstraintBounds top) :
    SelectorRootsWellFormed top.selectorMap := by
  simp only [TopLevelCircuit.selectorMap]
  exact selectorRootsWellFormed_deriveSelCompressMap
    top.constraintSystem
    top.n
    top.selectorActivations coherence.selectorDegree

/-- Selector compression covers every configured gate expression. -/
theorem gateSelectorsCovered :
    ∀ expression ∈ flatGates top.constraintSystem,
      expression.selectorsCovered
        (fun selector =>
          (top.selectorMap.lookup selector).isSome) = true := by
  simpa only [TopLevelCircuit.selectorMap] using
    gateSelectorsCovered_deriveSelCompressMap
      top.constraintSystem
      top.n
      top.selectorActivations
      top.gateSelectorsAllocated

/--
Every enabled constraint in the top-level operation stream has the corresponding
resolver gate polynomial witness.
-/
opaque polynomialWitness
    {k : ℕ}
    (coherence : TopLevelConstraintBounds top)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (sets : Fin pp.numProofs →
      List (PermSetEval CPoly))
    (chunks : Fin pp.numProofs →
      List (PermSetEval CPoly × List (CPoly × CPoly)))
    (l0 lLast lBlind : CPoly)
    (proofIndex : Fin pp.numProofs)
    (usableRows : ℕ)
    (hfixed : SelectorActivationsRealized top.selectorMap
      top.selectorActivations
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex usableRows))
    (enabled : EnabledGate Fp)
    (henabled :
      enabled ∈ operationEnabledGates (top.operations) 0)
    (constraint : Constraint Fp)
    (hconstraint : constraint ∈ enabled.gate.constraints) :
    EnabledGate.PolynomialWitness
      (constraintModelOfResolver
        (numProofs := pp.numProofs)
        (k := k)
        (top.toVerifierKey urs) ch poly sets chunks
        l0 lLast lBlind)
      proofIndex
      top.omega top.placement
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex usableRows)
      enabled constraint := by
  have hgate : enabled.gate ∈ top.constraintSystem.gates :=
    OperationsKeygenCoherent.gate
      top.keygenCoherent henabled
  have hselector :
      enabled.gate.selector.index <
        top.selectorCount :=
    List.forall_iff_forall_mem.mp top.gateSelectorsAllocated
      enabled.gate hgate
  have hlookupSome :
      (top.selectorMap.lookup
        enabled.gate.selector.index).isSome = true := by
    simpa [TopLevelCircuit.selectorMap] using
      deriveSelCompressMap_lookup_isSome_of_lt
        top.constraintSystem
        top.n
        top.selectorActivations hselector
  have hlookupPresent :
      (top.selectorMap.lookup
        enabled.gate.selector.index).isSome := by
    simpa using hlookupSome
  let compressed :=
    (top.selectorMap.lookup enabled.gate.selector.index).get hlookupPresent
  have hcompressed :
      top.selectorMap.lookup enabled.gate.selector.index =
        some compressed := (Option.some_get hlookupPresent).symm
  have hinterpret := coherence.resolverInterpretsGates
    (pp := pp) (urs := urs)
    poly proofIndex usableRows
    (top.placement enabled.region + enabled.row)
  have hscale :
      (selReplacement compressed).eval
        (Query.eval
          (resolverEnvironment
            (top.toVerifierKey urs) poly proofIndex usableRows)
          (fun _ => 0)
          (top.placement enabled.region + enabled.row)) ≠ 0 := by
    apply selectorScale_ne_zero_of_enabledGate
      top.selectorMap top.regionStarts (top.operations) 0
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex usableRows)
      (fun _ => 0) coherence.selectorRootsWellFormed
    · exact hfixed
    · exact henabled
    · exact hcompressed
  simpa only [top.toVerifierKey_omega] using
    enabledGatePolynomialWitnessOfResolver
    (numProofs := pp.numProofs)
    (k := k)
    (top.toVerifierKey urs)
    top.constraintSystem top.selectorMap ch poly sets chunks
    l0 lLast lBlind proofIndex
    top.placement usableRows
    enabled constraint hgate hconstraint
    (by
      rw [top.toVerifierKey_gates]
      exact top.verifierCS_gates_length)
    compressed hcompressed
    (by
      intro index hverifier hsource
      simpa only [top.toVerifierKey_gates, top.toVerifierKey_omega] using
        Halo2.TopLevelCircuit.verifierCS_gates_eval (top := top)
          (fun query =>
            (fixedQueryFeedOfResolver
              (top.toVerifierKey urs) poly query).eval
              (top.omega ^
                (top.placement enabled.region + enabled.row)))
          (fun query =>
            (adviceQueryFeedOfResolver
              (top.toVerifierKey urs) poly proofIndex query).eval
              (top.omega ^
                (top.placement enabled.region + enabled.row)))
          (fun query =>
            (instanceQueryFeedOfResolver
              (top.toVerifierKey urs) poly proofIndex query).eval
              (top.omega ^
                (top.placement enabled.region + enabled.row)))
          (Query.eval
            (resolverEnvironment
              (top.toVerifierKey urs) poly proofIndex usableRows)
            (fun _ => 0)
            (top.placement enabled.region + enabled.row))
          (gateSelectorsCovered (top := top)) hinterpret
          index (by
            simpa only [top.toVerifierKey_gates] using hverifier)
          hsource)
    hscale

/--
Specialize the top-level gate bridge to the canonical resolver model.

This removes the last opportunity for a gate caller to supply unrelated permutation
families or Lagrange-selector polynomials: they are the ones derived from the same
resolver and circuit-owned verification key.
-/
theorem canonicalConstraints
    {k : ℕ}
    (coherence : TopLevelConstraintBounds top)
    (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (proofIndex : Fin pp.numProofs)
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        top.n)
    (domain : ∀ row : ℕ,
      (top.omega ^ row) ^
        top.n = 1)
    (hfixed : SelectorActivationsRealized top.selectorMap
      top.selectorActivations
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))) :
    CircuitConstraintFamily.constraints .gate top.placement
      (resolverEnvironment
        (top.toVerifierKey urs) poly proofIndex
        (top.usableRowsAt top.domainExponent))
      (top.operations) 0 := by
  apply gate_constraints_of_polynomial_witnesses
    (top.constraintModel pp urs ch poly)
    proofIndex top.omega top.placement
    (resolverEnvironment
      (top.toVerifierKey urs) poly proofIndex
      (top.usableRowsAt top.domainExponent))
    (top.operations) 0 satisfaction domain
  intro enabled henabled constraint hconstraint
  let selectors :=
    canonicalLagrangePolynomials
      top.omega
      (top.toVerifierKey_blindingFactors_lt_n urs)
  rw [top.constraintModel_eq_constraintModelOfResolver]
  exact coherence.polynomialWitness ch poly
    (permutationSetsOfResolver
      (top.toVerifierKey urs) poly)
    (permutationChunksOfResolver
      (top.toVerifierKey urs) poly)
    selectors.1 selectors.2.1 selectors.2.2
    proofIndex (top.usableRowsAt top.domainExponent)
    hfixed enabled henabled constraint hconstraint

end TopLevelConstraintBounds

end Zcash.Snark
