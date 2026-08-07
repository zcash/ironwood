import Zcash.Circuits.Integration.ActionPermutationDomainCompute
import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Circuits.Integration.TopLevelConstraintModel
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Util.AssertNoSorry

/-!
# Action permutation domain and verifier layout

This module discharges the domain and chunk-layout premises retained by the
generic permutation semantics for the verifying key derived from
`actionCircuit`.

The keygen permutation itself belongs to the separate replay/assembly layer.
`cycleOfKeygenColumns` therefore accepts `fullSigma`, its active restriction,
the restriction equation, and the common-column identification explicitly.
-/

namespace Zcash.Snark

open Zcash.Arithmetic
  (deltaFp deltaFpOrder deltaFp_isPrimitiveRoot deltaFp_powers_injective
    omegaOf omegaOf_isPrimitiveRoot powFast_eq_pow scalarFieldOrder)

open CompPoly.CPolynomial
open Halo2
open Zcash.Circuits.Action (actionCircuit)

namespace ActionPermutationDomain

variable {G : Type} [AddCommGroup G] [Inhabited G]

abbrev actionShape (pp : ProofParams) : Shape :=
  actionCircuit.shape.withProofParams pp

/-- The derived Action VK has one verifier permutation set per chunk. -/
theorem chunkCount :
    actionCircuit.verifierCS.permutationChunks.length =
      actionCircuit.permutationSetCount :=
  verifierCS_permutationChunks_length actionCircuit

set_option maxRecDepth 100000 in
/-- Every Action permutation chunk has width at most the circuit's chunk width. -/
theorem chunkLength_le :
    ∀ i, i < actionCircuit.permutationSetCount →
      (actionCircuit.verifierCS.permutationChunks.getD i []).length ≤
        actionCircuit.chunkLen := by
  intro i hi
  have hiChunks :
      i <
        actionCircuit.verifierCS.permutationChunks.length := by
    rw [verifierCS_permutationChunks_length]
    exact hi
  rw [verifierCS_permutationChunks_getD_length actionCircuit i hiChunks]
  exact min_le_left _ _

/-- Resolver pairing preserves each concrete VK chunk's width. -/
theorem resolverPairsLength_le
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs) :
    ∀ i, i < actionCircuit.permutationSetCount →
      (ResolverPermutationPairs (actionCircuit.toVerifierKey urs) poly p i).length ≤
        actionCircuit.chunkLen := by
  intro i hi
  simpa only [actionCircuit.toVerifierKey_permutationChunks,
    actionCircuit.toVerifierKey_chunkLen,
    ResolverPermutationPairs, permutationChunkPairsOfResolver,
    List.length_map] using
    chunkLength_le i hi

set_option maxRecDepth 100000 in
/-- A resolver-backed chunk has exactly the compiler-derived suffix width. -/
theorem resolverPairsLength_eq_min
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs)
    (chunk : Fin actionCircuit.permutationSetCount) :
    (ResolverPermutationPairs
        (actionCircuit.toVerifierKey urs) poly p chunk).length =
      min actionCircuit.chunkLen
        (actionCircuit.permutationColumnCount -
          (chunk : ℕ) * actionCircuit.chunkLen) := by
  simp only [ResolverPermutationPairs,
    permutationChunkPairsOfResolver, List.length_map,
    actionCircuit.toVerifierKey_permutationChunks]
  have hi :
      (chunk : ℕ) <
        actionCircuit.verifierCS.permutationChunks.length := by
    rw [verifierCS_permutationChunks_length]
    exact chunk.isLt
  exact verifierCS_permutationChunks_getD_length actionCircuit chunk hi

set_option maxRecDepth 100000 in
/-- Every chunk value reference selects an in-range rotation-zero query-layout
entry, and every common-permutation index is in range. -/
theorem routingCoherent_of_derived
    (urs : URS G) :
    PermutationChunkRoutingCoherent (actionCircuit.toVerifierKey urs) := by
  have hadviceLayout :
      (actionCircuit.toVerifierKey urs).adviceQueryLayout =
        actionCircuit.adviceQueryLayout :=
    actionCircuit.toVerifierKey_adviceQueryLayout urs
  have hfixedLayout :
      (actionCircuit.toVerifierKey urs).fixedQueryLayout =
        actionCircuit.fixedQueryLayout :=
    actionCircuit.toVerifierKey_fixedQueryLayout urs
  have hinstanceLayout :
      (actionCircuit.toVerifierKey urs).instanceQueryLayout =
        actionCircuit.instanceQueryLayout :=
    actionCircuit.toVerifierKey_instanceQueryLayout urs
  rintro chunk hchunk ⟨ref, common⟩ href
  have hroute := routingCoherent chunk hchunk (ref, common) href
  rcases hroute with ⟨hrefCoherent, hcommon⟩
  constructor
  · cases ref with
    | advice i =>
        rcases hrefCoherent with ⟨hi, hrotation⟩
        change PermutationColumnRef.Coherent
          (actionCircuit.toVerifierKey urs) (.advice i)
        simp only [PermutationColumnRef.Coherent]
        refine ⟨?_, ?_, ?_⟩
        · simpa only [actionCircuit.shape_numAdviceQueries,
            TopLevelCircuit.adviceQueryCount] using hi
        · simpa only [hadviceLayout] using hi
        · simpa only [hadviceLayout] using hrotation
    | fixed i =>
        rcases hrefCoherent with ⟨hi, hrotation⟩
        change PermutationColumnRef.Coherent
          (actionCircuit.toVerifierKey urs) (.fixed i)
        simp only [PermutationColumnRef.Coherent]
        refine ⟨?_, ?_, ?_⟩
        · simpa only [actionCircuit.shape_numFixedQueries,
            TopLevelCircuit.fixedQueryCount] using hi
        · simpa only [hfixedLayout] using hi
        · simpa only [hfixedLayout] using hrotation
    | «instance» i =>
        rcases hrefCoherent with ⟨hi, hrotation⟩
        change PermutationColumnRef.Coherent
          (actionCircuit.toVerifierKey urs) (.instance i)
        simp only [PermutationColumnRef.Coherent]
        refine ⟨?_, ?_, ?_⟩
        · simpa only [actionCircuit.shape_numInstanceQueries,
            TopLevelCircuit.instanceQueryCount] using hi
        · simpa only [hinstanceLayout] using hi
        · simpa only [hinstanceLayout] using hrotation
  · simpa only [actionCircuit.shape_numPermutationColumns] using hcommon

/--
Flattening the derived verifier chunks and decoding their query references
recovers the compiler's original permutation-column order.
-/
theorem permutationColumnAddresses_eq
    (urs : URS G) :
    (actionCircuit.verifierCS.permutationChunks.flatten.map
        (fun reference =>
          permutationColumnAddress (actionCircuit.toVerifierKey urs) reference.1)) =
      (Keygen.permColsOf
        actionCircuit.constraintSystem).map
          Halo2.Layout.ColRef.toAny := by
  simpa only [actionCircuit.toVerifierKey_permutationChunks] using
    topLevelPermutationColumnAddresses_eq
      actionCircuit urs
        (routingCoherent_of_derived urs)

/-! ## Pasta permutation-name cosets -/

theorem scalarFieldOrder_sub_one_factorization :
    2 ^ 32 * deltaFpOrder = scalarFieldOrder - 1 := by
  norm_num [scalarFieldOrder,
    deltaFpOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

/-- `deltaFp = 5^(2^32)` lies in the odd-order factor of `Fpˣ`. -/
theorem deltaFp_pow_pastaOddFactor :
    deltaFp ^ deltaFpOrder = 1 := by
  exact deltaFp_isPrimitiveRoot.pow_eq_one

theorem pastaOddFactor_coprime_domain (k : ℕ) :
    Nat.Coprime (2 ^ k) deltaFpOrder := by
  apply Nat.Coprime.pow_left
  exact Odd.coprime_two_left (by
    norm_num [deltaFpOrder, scalarFieldOrder,
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])

/-- Every supported prefix of the permutation-column names `deltaFp^j`
occupies distinct cosets of a supported Pasta evaluation subgroup. -/
theorem deltaFp_domainCosets
    {k n : ℕ} (hk : k ≤ 32) (hn : n ≤ deltaFpOrder)
    (j j' : Fin n) (t : ℕ)
    (h :
      deltaFp ^ (j : ℕ) =
        omegaOf k ^ t * deltaFp ^ (j' : ℕ)) :
    j = j' := by
  have hj :
      (deltaFp ^ (j : ℕ)) ^ deltaFpOrder = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      deltaFp_pow_pastaOddFactor, one_pow]
  have hj' :
      (deltaFp ^ (j' : ℕ)) ^ deltaFpOrder = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      deltaFp_pow_pastaOddFactor, one_pow]
  have hpow := congrArg (fun x : Fp => x ^ deltaFpOrder) h
  change (deltaFp ^ (j : ℕ)) ^ deltaFpOrder =
    (omegaOf k ^ t * deltaFp ^ (j' : ℕ)) ^ deltaFpOrder at hpow
  rw [hj, mul_pow, hj', _root_.mul_one] at hpow
  have htMul : omegaOf k ^ (t * deltaFpOrder) = 1 := by
    rw [pow_mul]
    exact hpow.symm
  have hprimitive : IsPrimitiveRoot (omegaOf k) (2 ^ k) :=
    omegaOf_isPrimitiveRoot k hk
  have hdvdMul : 2 ^ k ∣ t * deltaFpOrder :=
    (hprimitive.pow_eq_one_iff_dvd _).mp htMul
  have hdvd : 2 ^ k ∣ t :=
    (pastaOddFactor_coprime_domain k).dvd_of_dvd_mul_right hdvdMul
  have ht : omegaOf k ^ t = 1 :=
    (hprimitive.pow_eq_one_iff_dvd _).mpr hdvd
  rw [ht, _root_.one_mul] at h
  exact deltaFp_powers_injective n hn h

/-! ## Derived evaluation-domain facts -/

/-- The active permutation prefix ends at the last usable Action row. -/
abbrev activeRows : ℕ :=
  actionCircuit.n - actionCircuit.blindingFactors - 1

theorem activeRows_le :
    activeRows ≤ actionCircuit.n := by
  unfold activeRows
  omega

/-- Canonical selectors and the derived usable-row count form the complete
generic permutation-domain record. In particular its `lastRotation` field is
the verifier's `omega^(-(blindingFactors + 1))` rotation. -/
theorem domain
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges actionCircuit.domainExponent Fp)
    (poly : CommitmentId → CPoly) :
    let model :=
      actionCircuit.constraintModel pp urs ch poly
    ResolverPermutationDomain (actionCircuit.toVerifierKey urs)
      model.l0 model.lLast model.lBlind
      actionCircuit.n
      activeRows := by
  exact ResolverPermutationDomain.ofCanonicalConstraintModel
    (actionCircuit.toVerifierKey urs) ch poly
      (actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
      (TopLevelAssignment.domainRowsInjective
        (top := actionCircuit) domainExponent_lt)
      (TopLevelAssignment.domainRoot
        (top := actionCircuit) domainExponent_lt)
      chunkCount

set_option maxRecDepth 100000 in
/-- Action chunk names are injective on any active prefix of the derived
evaluation domain. This is the `hnames` premise retained by
`ResolverPermutationCycle.ofKeygenColumns`. -/
theorem namesInjective
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs)
    {activeRows : ℕ} (hactive : activeRows ≤ actionCircuit.n) :
    Function.Injective fun c :
        ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p activeRows =>
      chunkRowName actionCircuit.omega Zcash.Arithmetic.deltaFp
        actionCircuit.chunkLen c.1 c.2.1 c.2.2 := by
  have hfull :
      Function.Injective fun c :
          ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p
            actionCircuit.n =>
        chunkRowName actionCircuit.omega Zcash.Arithmetic.deltaFp
          actionCircuit.chunkLen c.1 c.2.1 c.2.2 := by
    apply chunkRowName_injective_of_actual_coset
    · intro j
      apply pow_ne_zero
      change deltaFp ≠ 0
      rw [deltaFp, powFast_eq_pow]
      exact pow_ne_zero _ (by decide : (5 : Fp) ≠ 0)
    · exact TopLevelAssignment.domainRoot
        (top := actionCircuit) domainExponent_lt
    · intro i i' hi hi' heq
      have hfin :
          (⟨i, hi⟩ : Fin actionCircuit.n) =
            ⟨i', hi'⟩ :=
        TopLevelAssignment.domainRowsInjective
          (top := actionCircuit) domainExponent_lt heq
      exact Fin.ext_iff.mp hfin
    · intro j j' t hcoset
      change
        deltaFp ^
            ((j.1 : ℕ) * actionCircuit.chunkLen + (j.2 : ℕ)) =
          omegaOf actionCircuit.domainExponent ^ t *
            deltaFp ^
              ((j'.1 : ℕ) * actionCircuit.chunkLen + (j'.2 : ℕ)) at hcoset
      have hjWidth :
          (j.2 : ℕ) <
            min actionCircuit.chunkLen
              (actionCircuit.permutationColumnCount -
                (j.1 : ℕ) * actionCircuit.chunkLen) := by
        simpa only [resolverPairsLength_eq_min pp urs poly p j.1] using
          j.2.isLt
      have hj'Width :
          (j'.2 : ℕ) <
            min actionCircuit.chunkLen
              (actionCircuit.permutationColumnCount -
                (j'.1 : ℕ) * actionCircuit.chunkLen) := by
        simpa only [resolverPairsLength_eq_min pp urs poly p j'.1] using
          j'.2.isLt
      have hj :
          (j.1 : ℕ) * actionCircuit.chunkLen + (j.2 : ℕ) <
            actionCircuit.permutationColumnCount := by
        omega
      have hj' :
          (j'.1 : ℕ) * actionCircuit.chunkLen + (j'.2 : ℕ) <
            actionCircuit.permutationColumnCount := by
        omega
      have hcolumns :
          actionCircuit.permutationColumnCount = 15 :=
        permutationColumnCount_eq
      have hsupported :
          actionCircuit.permutationColumnCount ≤ deltaFpOrder := by
        rw [hcolumns]
        norm_num [deltaFpOrder, scalarFieldOrder,
          CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
      have hglobal :
          (⟨(j.1 : ℕ) * actionCircuit.chunkLen + (j.2 : ℕ), hj⟩ :
              Fin actionCircuit.permutationColumnCount) =
            ⟨(j'.1 : ℕ) * actionCircuit.chunkLen + (j'.2 : ℕ), hj'⟩ :=
        deltaFp_domainCosets
          (k := actionCircuit.domainExponent)
          (n := actionCircuit.permutationColumnCount)
          (Nat.le_of_lt_succ domainExponent_lt) hsupported
          ⟨_, hj⟩ ⟨_, hj'⟩ t hcoset
      have hindex :
          (j.1 : ℕ) * actionCircuit.chunkLen + (j.2 : ℕ) =
            (j'.1 : ℕ) * actionCircuit.chunkLen + (j'.2 : ℕ) :=
        congrArg Fin.val hglobal
      have hchunkLen :
          0 < actionCircuit.chunkLen :=
        constraintSystem_chunkLen_pos actionCircuit.constraintSystem
      have hjColumn :
          (j.2 : ℕ) < actionCircuit.chunkLen :=
        lt_of_lt_of_le j.2.isLt
          (resolverPairsLength_le pp urs poly p j.1 j.1.isLt)
      have hj'Column :
          (j'.2 : ℕ) < actionCircuit.chunkLen :=
        lt_of_lt_of_le j'.2.isLt
          (resolverPairsLength_le pp urs poly p j'.1 j'.1.isLt)
      have hchunk :
          (j.1 : ℕ) = (j'.1 : ℕ) := by
        have hjDiv :
            ((j.1 : ℕ) * actionCircuit.chunkLen + (j.2 : ℕ)) /
                actionCircuit.chunkLen =
              (j.1 : ℕ) := by
          calc
            _ =
                (actionCircuit.chunkLen * (j.1 : ℕ) + (j.2 : ℕ)) /
                  actionCircuit.chunkLen := by
                    rw [Nat.mul_comm]
            _ = (j.1 : ℕ) +
                (j.2 : ℕ) / actionCircuit.chunkLen :=
              Nat.mul_add_div hchunkLen _ _
            _ = (j.1 : ℕ) := by
              rw [Nat.div_eq_of_lt hjColumn, Nat.add_zero]
        have hj'Div :
            ((j'.1 : ℕ) * actionCircuit.chunkLen + (j'.2 : ℕ)) /
                actionCircuit.chunkLen =
              (j'.1 : ℕ) := by
          calc
            _ =
                (actionCircuit.chunkLen * (j'.1 : ℕ) + (j'.2 : ℕ)) /
                  actionCircuit.chunkLen := by
                    rw [Nat.mul_comm]
            _ = (j'.1 : ℕ) +
                (j'.2 : ℕ) / actionCircuit.chunkLen :=
              Nat.mul_add_div hchunkLen _ _
            _ = (j'.1 : ℕ) := by
              rw [Nat.div_eq_of_lt hj'Column, Nat.add_zero]
        rw [← hjDiv, hindex, hj'Div]
      have hchunkFin : j.1 = j'.1 := Fin.ext hchunk
      have hcolumn : (j.2 : ℕ) = (j'.2 : ℕ) := by
        have hprefix :
            (j.1 : ℕ) * actionCircuit.chunkLen =
              (j'.1 : ℕ) * actionCircuit.chunkLen :=
          congrArg
            (fun chunk => chunk * actionCircuit.chunkLen)
            hchunk
        apply Nat.add_left_cancel
        exact hindex.trans (by rw [hprefix])
      have hwidth :
          (ResolverPermutationPairs
              (actionCircuit.toVerifierKey urs) poly p j.1).length =
            (ResolverPermutationPairs
              (actionCircuit.toVerifierKey urs) poly p j'.1).length :=
        congrArg
          (fun chunk : ℕ =>
            (ResolverPermutationPairs
              (actionCircuit.toVerifierKey urs) poly p chunk).length)
          hchunk
      apply Sigma.ext hchunkFin
      exact (Fin.heq_ext_iff hwidth).mpr hcolumn
  intro c d hname
  have hwiden := widenPermutationChunkCell_injective
    (nc := actionCircuit.permutationSetCount)
    (width := fun i =>
      (ResolverPermutationPairs (actionCircuit.toVerifierKey urs) poly p i).length)
    hactive
  have hwname :
      chunkRowName actionCircuit.omega Zcash.Arithmetic.deltaFp
          actionCircuit.chunkLen
          (widenPermutationChunkCell hactive c).1
          (widenPermutationChunkCell hactive c).2.1
          (widenPermutationChunkCell hactive c).2.2 =
        chunkRowName actionCircuit.omega Zcash.Arithmetic.deltaFp
          actionCircuit.chunkLen
          (widenPermutationChunkCell hactive d).1
          (widenPermutationChunkCell hactive d).2.1
          (widenPermutationChunkCell hactive d).2.2 := by
    simpa only [widenPermutationChunkCell_fst,
      widenPermutationChunkCell_row,
      widenPermutationChunkCell_column] using hname
  exact hwiden (hfull hwname)

/-- Assemble the semantic cycle at any active-row prefix preserved by the
replayed full permutation. -/
def cycleOfKeygenColumnsAt
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs)
    {m : ℕ}
    (hactive : m ≤ actionCircuit.n)
    (fullSigma : Equiv.Perm
      (ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p
        actionCircuit.n))
    (sigma : Equiv.Perm
      (ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p
        m))
    (hcolumns : ∀
      (chunk : Fin actionCircuit.permutationSetCount)
      (column : Fin
        (ResolverPermutationPairs (actionCircuit.toVerifierKey urs) poly p chunk).length),
      (ResolverPermutationPairs
          (actionCircuit.toVerifierKey urs) poly p chunk)[column].2 =
        keygenSigmaColumn
          actionCircuit.omega Zcash.Arithmetic.deltaFp
          actionCircuit.chunkLen fullSigma chunk column)
    (hrestrict : ∀ c :
        ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p m,
      widenPermutationChunkCell hactive (sigma c) =
        fullSigma
          (widenPermutationChunkCell hactive c)) :
    ResolverPermutationCycle (actionCircuit.toVerifierKey urs) poly p m :=
  by
    simpa only [actionCircuit.toVerifierKey_n,
      actionCircuit.toVerifierKey_omega,
      actionCircuit.toVerifierKey_delta,
      actionCircuit.toVerifierKey_chunkLen] using
      ResolverPermutationCycle.ofKeygenColumns
        (actionCircuit.toVerifierKey urs) poly p hactive fullSigma sigma
          (TopLevelAssignment.domainRowsInjective
            (top := actionCircuit) domainExponent_lt)
          hcolumns hrestrict
          (namesInjective pp urs poly p hactive)

/-- Assemble the semantic cycle at the verifier-derived active-row boundary. -/
def cycleOfKeygenColumns
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs)
    (fullSigma : Equiv.Perm
      (ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p
        actionCircuit.n))
    (sigma : Equiv.Perm
      (ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p
        activeRows))
    (hcolumns : ∀
      (chunk : Fin actionCircuit.permutationSetCount)
      (column : Fin
        (ResolverPermutationPairs (actionCircuit.toVerifierKey urs) poly p chunk).length),
      (ResolverPermutationPairs
          (actionCircuit.toVerifierKey urs) poly p chunk)[column].2 =
        keygenSigmaColumn
          actionCircuit.omega Zcash.Arithmetic.deltaFp
          actionCircuit.chunkLen fullSigma chunk column)
    (hrestrict : ∀ c :
        ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p
          activeRows,
      widenPermutationChunkCell activeRows_le (sigma c) =
        fullSigma
          (widenPermutationChunkCell activeRows_le c)) :
    ResolverPermutationCycle (actionCircuit.toVerifierKey urs) poly p
      activeRows :=
  cycleOfKeygenColumnsAt pp urs poly p activeRows_le
    fullSigma sigma hcolumns hrestrict

assert_no_sorry routingCoherent_of_derived
assert_no_sorry deltaFp_domainCosets
assert_no_sorry domain
assert_no_sorry namesInjective
assert_no_sorry cycleOfKeygenColumnsAt
assert_no_sorry cycleOfKeygenColumns

end ActionPermutationDomain

end Zcash.Snark
