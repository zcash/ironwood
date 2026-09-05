import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.Canonical.PolynomialEnvironment
import Zcash.Snark.Soundness.Multiopen.Decode
import Zcash.Snark.Soundness.Deployed.Binding
import Zcash.Snark.Soundness.Multiopen.Compat

/-!
# Public-instance commitment provenance

Halo 2 commits to public-instance values in the Lagrange basis, while the multiopen extractor
returns coefficient vectors in the monomial basis.  This file gives the basis-independent algebra
joining those two views.  It is generic in the evaluation domain, the commitment group, and the
public row vector; the Action circuit only decides which rows form its external statement.
-/

namespace Zcash.Snark

open Polynomial CompPoly

set_option maxHeartbeats 20000

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The first `n` monomial coefficients of a polynomial. -/
def polynomialCoefficients (n : ℕ) (p : CPoly) : Fin n → Fp :=
  fun i => p.coeff (i : ℕ)

/-- A polynomial of degree below `n` is reconstructed by its length-`n` coefficient vector. -/
theorem coeffsToPoly_polynomialCoefficients {n : ℕ} {p : CPoly}
    (hdegree : p.natDegree < n) :
    coeffsToPoly (polynomialCoefficients n p) = p := by
  apply CPolynomial.toPoly_injective
  rw [coeffsToPoly, CPolynomial.toPoly_sum]
  simp only [CPolynomial.toPoly_mul, CPolynomial.C_toPoly, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly, polynomialCoefficients, CPolynomial.coeff_toPoly]
  simpa only [← Fin.sum_univ_eq_sum_range] using
    (p.toPoly.as_sum_range_C_mul_X_pow'
      (by rwa [← CPolynomial.natDegree_toPoly])).symm

/-- Every row vector is the sum of its scaled coordinate vectors after interpolation. -/
theorem rowPolynomial_eq_sum_single {n : ℕ}
    (omega : Fp) (values : Fin n → Fp) :
    rowPolynomial omega values =
      ∑ i : Fin n, values i • rowPolynomial omega (Pi.single i 1) := by
  let interpolation :=
    Lagrange.interpolate Finset.univ (fun i : Fin n => omega ^ (i : ℕ))
  apply CPolynomial.toPoly_injective
  rw [toPoly_rowPolynomial, CPolynomial.toPoly_sum]
  simp_rw [CPolynomial.toPoly_smul, toPoly_rowPolynomial]
  change interpolation values =
    ∑ i : Fin n, values i • interpolation (Pi.single i 1)
  calc
    interpolation values =
        interpolation (∑ i : Fin n, values i • Pi.single i 1) := by
          congr 1
          funext j
          rw [Fintype.sum_apply]
          symm
          calc
            (∑ i : Fin n, (values i • Pi.single i 1) j) =
                ∑ i : Fin n, Pi.single i (values i) j := by
                  apply Finset.sum_congr rfl
                  intro i _
                  by_cases hij : i = j
                  · subst i
                    simp
                  · simp [Pi.single_eq_of_ne (Ne.symm hij)]
            _ = values j := Fintype.sum_pi_single j values
    _ = ∑ i : Fin n, values i • interpolation (Pi.single i 1) := by
      simp only [map_sum, map_smul]

/-- Taking coefficients commutes with the coordinate decomposition of an interpolated row vector. -/
theorem polynomialCoefficients_rowPolynomial_eq_sum_single {n : ℕ}
    (omega : Fp) (values : Fin n → Fp) :
    polynomialCoefficients n (rowPolynomial omega values) =
      ∑ i : Fin n, values i •
        polynomialCoefficients n (rowPolynomial omega (Pi.single i 1)) := by
  rw [rowPolynomial_eq_sum_single]
  funext j
  simp only [polynomialCoefficients, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [CPolynomial.coeff_toPoly, CPolynomial.toPoly_sum]
  simp only [CPolynomial.toPoly_smul, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    smul_eq_mul, CPolynomial.coeff_toPoly]

/-- The monomial coefficient vector of the zero-padded public-instance row polynomial. -/
def instanceCoefficients (n : ℕ)
    (omega : Fp) (values : List Fp) : Fin n → Fp :=
  polynomialCoefficients n (instanceRowPolynomial n omega values)

/-- The canonical instance coefficients decode to the zero-padded row polynomial. -/
theorem coeffsToPoly_instanceCoefficients {n : ℕ}
    {omega : Fp} {values : List Fp}
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hn : 0 < n) :
    coeffsToPoly (instanceCoefficients n omega values) =
      instanceRowPolynomial n omega values :=
  coeffsToPoly_polynomialCoefficients (rowPolynomial_natDegree_lt hrows hn)

/--
A Lagrange commitment key compatible with a monomial-basis URS.

The pointwise equation is the setup relation: generator `i` commits to the coefficients of the
Lagrange polynomial which is one at row `i` and zero at every other row.  It is independent of any
circuit or verifying key.
-/
structure LagrangeCommitmentKey (urs : URS G) (omega : Fp) where
  generators : Fin (2 ^ urs.k) → G
  generator_eq : ∀ i, generators i =
    commit urs (polynomialCoefficients (2 ^ urs.k)
      (rowPolynomial omega (Pi.single i 1)))

namespace LagrangeCommitmentKey

/-- The canonical Lagrange commitment key determined directly by the monomial URS. -/
def canonical (urs : URS G) (omega : Fp) :
    LagrangeCommitmentKey urs omega where
  generators i :=
    commit urs (polynomialCoefficients (2 ^ urs.k)
      (rowPolynomial omega (Pi.single i 1)))
  generator_eq _ := rfl

/-- Commitment keys are determined by their generator family; the compatibility
field is proof-irrelevant. -/
@[ext] theorem ext {urs : URS G} {omega : Fp}
    {left right : LagrangeCommitmentKey urs omega}
    (hgenerators : left.generators = right.generators) :
    left = right := by
  cases left
  cases right
  simp_all

/-- **A URS and a domain generator admit at most one commitment key.** `generator_eq` pins every
generator to the monomial commitment of its Lagrange row, so the structure records no choice: the
constructors below (`ofPrefix`, `ofFullList`) and any circuit-supplied key agree on the nose.

This is what lets a fixture discharge a setup obligation against whichever key a downstream
statement happens to name. -/
instance instSubsingleton {urs : URS G} {omega : Fp} :
    Subsingleton (LagrangeCommitmentKey urs omega) :=
  ⟨fun left right =>
    ext (funext fun i => by rw [left.generator_eq, right.generator_eq])⟩

/--
Build a full commitment key from a certified exported prefix.

Parameter fixtures only need to export generators reached by nonzero public rows.  Beyond that
prefix, this constructor fills the key with the canonical monomial-URS commitment itself, so the
setup certificate has one obligation per exported generator rather than one per domain row.
-/
def ofPrefix (urs : URS G) (omega : Fp) (generatorsPrefix : List G)
    (hprefix : ∀ i : Fin (2 ^ urs.k), (i : ℕ) < generatorsPrefix.length →
      generatorsPrefix.getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial omega (Pi.single i 1)))) :
    LagrangeCommitmentKey urs omega where
  generators := fun i =>
    if (i : ℕ) < generatorsPrefix.length then generatorsPrefix.getD (i : ℕ) 0
    else
      commit urs (polynomialCoefficients (2 ^ urs.k)
        (rowPolynomial omega (Pi.single i 1)))
  generator_eq := by
    intro i
    by_cases hi : (i : ℕ) < generatorsPrefix.length
    · rw [if_pos hi]
      exact hprefix i hi
    · rw [if_neg hi]

/--
Build a commitment key from a complete executable generator list.

Unlike `ofPrefix`, this constructor has no interpolated fallback and is therefore
computable. The caller proves the generator equation for every domain index.
-/
def ofFullList (urs : URS G) (omega : Fp) (generators : List G)
    (hgenerators : ∀ i : Fin (2 ^ urs.k),
      generators.getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial omega (Pi.single i 1)))) :
    LagrangeCommitmentKey urs omega where
  generators := fun i => generators.getD (i : ℕ) 0
  generator_eq := hgenerators

@[simp] theorem ofFullList_generator
    (urs : URS G) (omega : Fp) (generators : List G)
    (hgenerators : ∀ i : Fin (2 ^ urs.k),
      generators.getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial omega (Pi.single i 1))))
    (i : Fin (2 ^ urs.k)) :
    (ofFullList urs omega generators hgenerators).generators i =
      generators.getD (i : ℕ) 0 := by
  simp only [ofFullList]

@[simp] theorem ofPrefix_generator_of_lt
    (urs : URS G) (omega : Fp) (generatorsPrefix : List G)
    (hprefix : ∀ i : Fin (2 ^ urs.k), (i : ℕ) < generatorsPrefix.length →
      generatorsPrefix.getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial omega (Pi.single i 1))))
    (i : Fin (2 ^ urs.k)) (hi : (i : ℕ) < generatorsPrefix.length) :
    (ofPrefix urs omega generatorsPrefix hprefix).generators i =
      generatorsPrefix.getD (i : ℕ) 0 := by
  simp [ofPrefix, hi]

/--
Commit a finite public column using only an exported Lagrange-generator prefix.

This is the shape used by parameter fixtures: the list contains every generator reached by
`values`, and rows beyond `values.length` are implicitly zero.
-/
def commitPrefix (urs : URS G) (generatorsPrefix : List G)
    (values : List Fp) (blind : Fp) : G :=
  (∑ i ∈ Finset.range values.length,
    values.getD i 0 • generatorsPrefix.getD i 0) + blind • urs.w

/-- Executable fixture spelling of `commitPrefix`, using canonical representatives and `nsmul`. -/
def commitPrefixNat (urs : URS G) (generatorsPrefix : List G)
    (values : List Fp) (blind : Fp) : G :=
  ((List.range values.length).map fun i =>
    (values.getD i 0).val • generatorsPrefix.getD i 0).sum + blind.val • urs.w

/-- The fixture's canonical-representative MSM is the abstract field-module commitment. -/
theorem commitPrefixNat_eq_commitPrefix
    (urs : URS G) (generatorsPrefix : List G)
    (values : List Fp) (blind : Fp) :
    commitPrefixNat urs generatorsPrefix values blind =
      commitPrefix urs generatorsPrefix values blind := by
  have scalar_nsmul_eq_smul : ∀ (c : Fp) (point : G), c.val • point = c • point :=
    fun c point => by
      rw [← Nat.cast_smul_eq_nsmul Fp c.val point, ZMod.natCast_rightInverse c]
  rw [commitPrefixNat, commitPrefix]
  simp_rw [scalar_nsmul_eq_smul]
  rw [← List.sum_toFinset
      (fun i => values.getD i 0 • generatorsPrefix.getD i 0) List.nodup_range,
    List.toFinset_range]

/-- Halo 2's public-instance commitment, including its blinding-generator component. -/
def commitRows {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : Fin (2 ^ urs.k) → Fp) (blind : Fp) : G :=
  commitGen key.generators values + blind • urs.w

/-- A compatible Lagrange commitment is the monomial commitment to the interpolated row polynomial. -/
theorem commitRows_eq {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : Fin (2 ^ urs.k) → Fp) (blind : Fp) :
    key.commitRows values blind =
      commit urs (polynomialCoefficients (2 ^ urs.k) (rowPolynomial omega values)) +
        blind • urs.w := by
  classical
  rw [commitRows, commitGen]
  simp_rw [key.generator_eq]
  rw [polynomialCoefficients_rowPolynomial_eq_sum_single]
  simp only [commit, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

/-- Commit a finite public-instance column after zero-padding it to the full domain. -/
def commitInstance {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : List Fp) (blind : Fp) : G :=
  key.commitRows (zeroPaddedRows (n := 2 ^ urs.k) values) blind

/-- The finite-column spelling of `commitRows_eq`. -/
theorem commitInstance_eq {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : List Fp) (blind : Fp) :
    key.commitInstance values blind =
      commit urs (instanceCoefficients (2 ^ urs.k) omega values) +
        blind • urs.w := by
  simpa [commitInstance, instanceCoefficients, instanceRowPolynomial] using
    key.commitRows_eq (zeroPaddedRows (n := 2 ^ urs.k) values) blind

/-- Trailing zero rows do not change a committed instance column: the commitment zero-pads every
column to the domain, so columns differing only by trailing zeros are indistinguishable at
commitment level.  This is the collision behind the shorter-column alias — a column that stops
before a trailing flag row commits exactly as the full column carrying that flag as `0`;
`assembleNonInteractiveInstances?_padColumns` (`Verifier/Deployed.lean`) states the resulting
acceptance invariance at the raw verifier entry. -/
theorem commitInstance_append_replicate_zero {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : List Fp) (m : ℕ) (blind : Fp) :
    key.commitInstance (values ++ List.replicate m 0) blind =
      key.commitInstance values blind := by
  unfold commitInstance
  rw [zeroPaddedRows_append_replicate_zero]

/--
The full key made by `ofPrefix` commits any column contained in the certified prefix exactly as the
finite-prefix implementation does.
-/
theorem ofPrefix_commitInstance_eq
    (urs : URS G) (omega : Fp) (generatorsPrefix : List G)
    (hprefix : ∀ i : Fin (2 ^ urs.k), (i : ℕ) < generatorsPrefix.length →
      generatorsPrefix.getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial omega (Pi.single i 1))))
    (values : List Fp) (blind : Fp)
    (hvaluesPrefix : values.length ≤ generatorsPrefix.length)
    (hvaluesDomain : values.length ≤ 2 ^ urs.k) :
    (ofPrefix urs omega generatorsPrefix hprefix).commitInstance values blind =
      commitPrefix urs generatorsPrefix values blind := by
  classical
  rw [commitInstance, commitRows, commitGen, commitPrefix]
  congr 1
  let summand : ℕ → G := fun i =>
    if hi : i < 2 ^ urs.k then
      values.getD i 0 •
        (ofPrefix urs omega generatorsPrefix hprefix).generators ⟨i, hi⟩
    else 0
  have hdomainSum :
      (∑ i : Fin (2 ^ urs.k),
          values.getD (i : ℕ) 0 •
            (ofPrefix urs omega generatorsPrefix hprefix).generators i) =
        ∑ i ∈ Finset.range (2 ^ urs.k), summand i := by
    rw [← Fin.sum_univ_eq_sum_range summand (2 ^ urs.k)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [summand, dif_pos i.isLt]
  simp only [zeroPaddedRows]
  rw [hdomainSum]
  symm
  calc
    (∑ i ∈ Finset.range values.length,
        values.getD i 0 • generatorsPrefix.getD i 0) =
        ∑ i ∈ Finset.range values.length, summand i := by
      apply Finset.sum_congr rfl
      intro i hiValues
      have hiValues' := Finset.mem_range.mp hiValues
      have hiDomain : i < 2 ^ urs.k := lt_of_lt_of_le hiValues' hvaluesDomain
      have hiPrefix : i < generatorsPrefix.length :=
        lt_of_lt_of_le hiValues' hvaluesPrefix
      simp only [summand, dif_pos hiDomain,
        ofPrefix_generator_of_lt urs omega generatorsPrefix hprefix ⟨i, hiDomain⟩
          hiPrefix]
    _ = ∑ i ∈ Finset.range (2 ^ urs.k), summand i := by
      apply Finset.sum_subset (Finset.range_mono hvaluesDomain)
      intro i hiDomain hiValues
      have hvalues : values.length ≤ i := by
        simpa only [Finset.mem_range, not_lt] using hiValues
      simp only [summand, dif_pos (Finset.mem_range.mp hiDomain),
        List.getD_eq_default values 0 hvalues, zero_smul]

/--
A complete executable generator list commits finite rows exactly as the corresponding
prefix computation. This is the computable full-list counterpart of
`ofPrefix_commitInstance_eq`.
-/
theorem ofFullList_commitInstance_eq
    (urs : URS G) (omega : Fp) (generators : List G)
    (hlen : generators.length = 2 ^ urs.k)
    (hgenerators : ∀ i : Fin (2 ^ urs.k),
      generators.getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial omega (Pi.single i 1))))
    (values : List Fp) (blind : Fp)
    (hvaluesDomain : values.length ≤ 2 ^ urs.k) :
    (ofFullList urs omega generators hgenerators).commitInstance values blind =
      commitPrefix urs generators values blind := by
  let hprefix : ∀ i : Fin (2 ^ urs.k),
      (i : ℕ) < generators.length →
      generators.getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial omega (Pi.single i 1))) :=
    fun i _ => hgenerators i
  have hkey :
      ofFullList urs omega generators hgenerators =
        ofPrefix urs omega generators hprefix := by
    ext i
    have hi : (i : ℕ) < generators.length := by
      rw [hlen]
      exact i.isLt
    simp only [ofFullList_generator,
      ofPrefix_generator_of_lt urs omega generators hprefix i hi]
  rw [hkey]
  apply ofPrefix_commitInstance_eq
  · simpa only [hlen] using hvaluesDomain
  · exact hvaluesDomain

end LagrangeCommitmentKey

/-- Compares an augmented instance opening with its executable coefficients, returning equality
of all coordinates or their explicit nontrivial relation. -/
def instanceOpening_eq_or_relation
    {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : List Fp) (blind : Fp)
    (decoded : Fin (2 ^ urs.k) → Fp) (uComp wComp : Fp)
    (hopen :
      commit urs decoded + uComp • urs.u + wComp • urs.w =
        key.commitInstance values blind) :
    (decoded = instanceCoefficients (2 ^ urs.k) omega values ∧
      uComp = 0 ∧ wComp = blind) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  haveI : DecidableEq Fp := inferInstanceAs (DecidableEq (ZMod Zcash.Arithmetic.scalarFieldOrder))
  let expected := instanceCoefficients (2 ^ urs.k) omega values
  have hcollision :
      commitGen urs.g decoded + uComp • urs.u + wComp • urs.w =
        commitGen urs.g expected + (0 : Fp) • urs.u + blind • urs.w := by
    rw [← commit_eq_commitGen, ← commit_eq_commitGen]
    simpa [expected, key.commitInstance_eq values blind] using hopen
  exact
    if heq : decoded = expected ∧ uComp = 0 ∧ wComp = blind then
      PSum.inl heq
    else
      PSum.inr (NontrivialRelation.ofCombinationCollision hcollision heq)

/--
At the polynomial interface, an augmented opening of the statement-derived instance commitment is
the canonical zero-padded row polynomial, or it computes the same AGM relation.
-/
def coeffsToPoly_eq_instanceRowPolynomial_or_relation
    {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : List Fp) (blind : Fp)
    (decoded : Fin (2 ^ urs.k) → Fp) (uComp wComp : Fp)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) => omega ^ (i : ℕ))
    (hopen :
      commit urs decoded + uComp • urs.u + wComp • urs.w =
        key.commitInstance values blind) :
    coeffsToPoly decoded =
        instanceRowPolynomial (2 ^ urs.k) omega values ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w :=
  bindOrRelationWitness
    (instanceOpening_eq_or_relation key values blind decoded uComp wComp hopen)
    fun hcoordinates => by
      rw [hcoordinates.1]
      exact coeffsToPoly_instanceCoefficients hrows (Nat.two_pow_pos urs.k)

end Zcash.Snark
