import Zcash.Snark.Soundness.Canonical.InstanceCommitment
import Zcash.Snark.Soundness.Ipa.InnerProduct
import Zcash.Snark.Keygen.Pipeline
import Zcash.Arithmetic.LagrangeBasis
import Zcash.Arithmetic.InvDft

/-!
# From the closed Lagrange rows to the commitment keys

`Zcash.Arithmetic.LagrangeBasis` puts the `i`-th Lagrange basis polynomial in closed
coefficient form (`ℓ_i = n⁻¹ · Σ_t ω^{-i·t} Xᵗ`). This module spends that form on the
verifier-side objects: the interpolated Kronecker column IS the closed polynomial, so each
`LagrangeCommitmentKey.generator_eq` obligation becomes a computable commitment identity, and
the fixed- and permutation-column commitments agree with `commitInstance` against the
full-list key.

`derivedUrsGLagrange_generator_eq` closes the loop from the other side: the `i`-th entry of
the derived Lagrange basis (the scaled inverse group-FFT of the monomial URS) is the monomial
commitment to that same closed row. It lives here rather than beside the FFT specification
because `commit` is verifier-side vocabulary (`Soundness/Ipa/InnerProduct.lean`) and the
arithmetic tier does not import it.
-/

namespace Zcash.Snark.Keygen

open Halo2.Layout (permColsOf)

open Zcash.Arithmetic (derivedUrsGLagrange derivedUrsGLagrange_getD domainSize_cast_ne_zero
  lagrangeBasisClosed lagrangeBasisClosed_coeff lagrangeBasisClosed_eval
  lagrangeBasisClosed_natDegree_lt omegaInvOf_eq_inv omegaOf omegaOf_isPrimitiveRoot
  omegaOf_powers_injective)

open Polynomial
open CompElliptic.Curves.Pasta
/-- The interpolated Kronecker column IS the closed form: both have degree below the
node count and agree on every node. -/
theorem rowPolynomial_single_eq_closed (k : ℕ) (hk : k ≤ 32) (i : Fin (2 ^ k)) :
    rowPolynomial (omegaOf k) (Pi.single i (1 : Fp)) = lagrangeBasisClosed k i := by
  classical
  apply CompPoly.CPolynomial.toPoly_injective
  symm
  rw [toPoly_rowPolynomial]
  apply Lagrange.eq_interpolate_of_eval_eq _ (omegaOf_powers_injective k hk).injOn
  · rw [Finset.card_univ, Fintype.card_fin]
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    rw [← CompPoly.CPolynomial.natDegree_toPoly]
    exact_mod_cast lagrangeBasisClosed_natDegree_lt k i
  · intro j _
    rw [← CompPoly.CPolynomial.eval_toPoly, lagrangeBasisClosed_eval k hk i j, Pi.single_apply]

/-- The Lagrange commitment key's required coefficient vector, in computable closed
form: `ℓ_i`'s `t`-th coefficient is `n⁻¹ · ω^{-i·t}`. -/
theorem polynomialCoefficients_single_closed (k : ℕ) (hk : k ≤ 32)
    (i t : Fin (2 ^ k)) :
    polynomialCoefficients (2 ^ k) (rowPolynomial (omegaOf k) (Pi.single i (1 : Fp))) t =
      (2 ^ k : Fp)⁻¹ * (omegaOf k)⁻¹ ^ ((i : ℕ) * (t : ℕ)) := by
  rw [polynomialCoefficients, rowPolynomial_single_eq_closed k hk i]
  exact lagrangeBasisClosed_coeff k i t

theorem permPolysOf_length (k : ℕ) (cs : Halo2.ConstraintSystem Fp)
    (ops : Halo2.Operations Fp) :
    (permPolysOf k cs ops).length = (permColsOf cs).length := by
  simp [permPolysOf]

theorem permPolysOf_getD_length (k : ℕ) (cs : Halo2.ConstraintSystem Fp)
    (ops : Halo2.Operations Fp) (c : ℕ) (hc : c < (permColsOf cs).length) :
    ((permPolysOf k cs ops).getD c []).length = 2 ^ k := by
  have hcl : c < (permPolysOf k cs ops).length := by
    rw [permPolysOf_length]; exact hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl]
  simp [permPolysOf]

/--
The executable Lagrange MSM of one full-domain row vector agrees with the computable
full-list key's instance commitment. This isolates the common commitment algebra from
the fixed- and permutation-column list plumbing.
-/
theorem commitLagrangeFastWith_eq_ofFullList_commitInstance
    {G : Type} [AddCommGroup G] [Module Fp G] [Inhabited G]
    (urs : URS G) (omega : Fp)
    (hlen : (derivedUrsGLagrange urs).length = 2 ^ urs.k)
    (hgenerators : ∀ i : Fin (2 ^ urs.k),
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial omega
            (Pi.single i (1 : Fp)))))
    (values : List Fp) (hvalues : values.length = 2 ^ urs.k) :
    Fast.Msm.commitLagrangeFastWith
        Fast.Msm.defaultWindow urs.w
        (derivedUrsGLagrange urs) values =
      (LagrangeCommitmentKey.ofFullList
        urs omega (derivedUrsGLagrange urs)
        hgenerators).commitInstance values 1 := by
  rw [LagrangeCommitmentKey.ofFullList_commitInstance_eq
    urs omega _ hlen hgenerators values 1 (by rw [hvalues])]
  rw [Fast.Msm.commitLagrangeFastWith_eq
    Fast.Msm.defaultWindow
    (by norm_num [Fast.Msm.defaultWindow]) urs.w]
  rw [← LagrangeCommitmentKey.commitPrefixNat_eq_commitPrefix,
    Fast.Msm.commitLagrangeSpec,
    LagrangeCommitmentKey.commitPrefixNat]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul Fp ((1 : Fp).val) urs.w,
    ZMod.natCast_rightInverse (1 : Fp), one_smul]

/-- **The derived σ commitments are Lagrange-key commitments of the derived σ rows**:
the executable Pippenger pipeline (with halo2's default blind, the `w` generator) equals
the abstract prefix-key commitment. The two hypotheses are the per-URS setup facts:
the derived basis length and the generator identities in closed coefficient form. -/
theorem permutationCommitmentsOf_getD_eq_commitInstance
    {G : Type} [AddCommGroup G] [Module Fp G] [Inhabited G]
    (urs : URS G) (cs : Halo2.ConstraintSystem Fp) (ops : Halo2.Operations Fp)
    (hlen : (derivedUrsGLagrange urs).length = 2 ^ urs.k)
    (hprefix : ∀ i : Fin (2 ^ urs.k), (i : ℕ) < (derivedUrsGLagrange urs).length →
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial (omegaOf urs.k) (Pi.single i (1 : Fp)))))
    (c : ℕ) (hc : c < (permColsOf cs).length) :
    (permutationCommitmentsOf urs.w (derivedUrsGLagrange urs) urs.k cs ops).getD c 0 =
      (LagrangeCommitmentKey.ofPrefix urs (omegaOf urs.k) (derivedUrsGLagrange urs)
          hprefix).commitInstance
        ((permPolysOf urs.k cs ops).getD c []) 1 := by
  classical
  have hrowlen : ((permPolysOf urs.k cs ops).getD c []).length = 2 ^ urs.k :=
    permPolysOf_getD_length urs.k cs ops c hc
  rw [LagrangeCommitmentKey.ofPrefix_commitInstance_eq urs (omegaOf urs.k) _ hprefix _ 1
    (by rw [hrowlen, hlen]) (by rw [hrowlen])]
  have hcl : c < (permPolysOf urs.k cs ops).length := by
    rw [permPolysOf_length]; exact hc
  have hget : ((permPolysOf urs.k cs ops).map
      (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow urs.w
        (derivedUrsGLagrange urs))).getD c 0 =
      Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow urs.w
        (derivedUrsGLagrange urs) ((permPolysOf urs.k cs ops).getD c []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hcl,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl]
    rfl
  rw [permutationCommitmentsOf, permutationCommitmentsWith,
    List.parMap_eq_map, hget,
    Fast.Msm.commitLagrangeFastWith_eq Fast.Msm.defaultWindow
      (by norm_num [Fast.Msm.defaultWindow]) urs.w]
  rw [← LagrangeCommitmentKey.commitPrefixNat_eq_commitPrefix,
    Fast.Msm.commitLagrangeSpec, LagrangeCommitmentKey.commitPrefixNat]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul Fp ((1 : Fp).val) urs.w,
    ZMod.natCast_rightInverse (1 : Fp), one_smul]

/-- The prefix setup follows from the closed formula for interpolation coefficients. -/
theorem ofPrefix_setup_of_closed {G : Type} [AddCommGroup G] [Module Fp G]
    [Inhabited G] (urs : URS G) (hk : urs.k ≤ 32)
    (hgen : ∀ i : Fin (2 ^ urs.k),
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs fun t : Fin (2 ^ urs.k) =>
          (2 ^ urs.k : Fp)⁻¹ * (omegaOf urs.k)⁻¹ ^ ((i : ℕ) * (t : ℕ))) :
    ∀ i : Fin (2 ^ urs.k), (i : ℕ) < (derivedUrsGLagrange urs).length →
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial (omegaOf urs.k) (Pi.single i (1 : Fp)))) := by
  intro i _
  rw [hgen i]
  congr 1
  funext t
  rw [polynomialCoefficients_single_closed urs.k hk i t]

/-- The closed-form generator commitment in the fixture's executable spelling:
canonical-representative scalars and `nsmul`. -/
def commitClosedNat {G : Type} [AddCommGroup G] (urs : URS G)
    (i : Fin (2 ^ urs.k)) : G :=
  (List.ofFn fun t : Fin (2 ^ urs.k) =>
    ((2 ^ urs.k : Fp)⁻¹ * (omegaOf urs.k)⁻¹ ^ ((i : ℕ) * (t : ℕ))).val • urs.g t).sum

/-- The executable closed-form commitment is the abstract one. -/
theorem commitClosedNat_eq {G : Type} [AddCommGroup G] [Module Fp G]
    (urs : URS G) (i : Fin (2 ^ urs.k)) :
    commitClosedNat urs i =
      commit urs (fun t : Fin (2 ^ urs.k) =>
        (2 ^ urs.k : Fp)⁻¹ * (omegaOf urs.k)⁻¹ ^ ((i : ℕ) * (t : ℕ))) := by
  rw [commitClosedNat, commit, List.sum_ofFn]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Nat.cast_smul_eq_nsmul Fp, ZMod.natCast_rightInverse]

/-- **The derived Lagrange generators in closed form** (the roadmap's `generator_eq`): the
`i`-th entry of `derivedUrsGLagrange` is the monomial commitment to the closed Lagrange
coefficient row `n⁻¹ · ω^(−i·t)`. This is exactly the `hgen` input of
`ofPrefix_setup_of_closed` above, which turns it into the `hgenerators`/`hprefix` setup
obligations of the fixed- and permutation-commitment identification theorems. -/
theorem derivedUrsGLagrange_generator_eq {G : Type} [AddCommGroup G] [Inhabited G]
    [Module Fp G] (urs : URS G) (hk : urs.k ≤ 32) (i : Fin (2 ^ urs.k)) :
    (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
      commit urs fun t : Fin (2 ^ urs.k) =>
        (2 ^ urs.k : Fp)⁻¹ * (omegaOf urs.k)⁻¹ ^ ((i : ℕ) * (t : ℕ)) := by
  rw [derivedUrsGLagrange_getD urs hk i, commit, omegaInvOf_eq_inv urs.k hk]

end Zcash.Snark.Keygen

namespace Halo2.TopLevelCircuit

open Zcash.Snark Zcash.Arithmetic CompElliptic.Curves.Pasta

/-- The circuit-derived VK's fixed commitment at one in-range column is the
full-list commitment of the corresponding keygen row vector. -/
theorem fixedCommitments_getD_eq_commitInstance
    {G : Type} [AddCommGroup G] [Module Fp G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    [TopLevelShape top] [CircuitFieldSupport top]
    (urs : URS G)
    (hk : top.domainExponent = urs.k)
    (column : ℕ) (hcolumn : column < top.fixedColumnCount) :
    (top.fixedCommitments urs).getD column 0 =
      (LagrangeCommitmentKey.canonical urs top.omega).commitInstance
          (top.fixedRows.getD column []) 1 := by
  have hkUrs : urs.k ≤ 32 := by
    rw [← hk]
    exact Nat.le_of_lt_succ top.domainExponent_lt
  have homega : top.omega = omegaOf urs.k := by
    simp only [TopLevelCircuit.omega, Zcash.Arithmetic.pastaDomain_omega_eq, hk]
  have hlen := derivedUrsGLagrange_length urs
  have hgenerators : ∀ i : Fin (2 ^ urs.k),
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial top.omega (Pi.single i (1 : Fp)))) := by
    intro i
    simpa only [homega] using
      Keygen.ofPrefix_setup_of_closed urs hkUrs
        (Keygen.derivedUrsGLagrange_generator_eq urs hkUrs) i
        (by rw [hlen]; exact i.isLt)
  have hcolumnRows : column < top.fixedRows.length := by
    simpa only [top.fixedRows_length] using hcolumn
  have hget :
      (top.fixedRows.map
        (Fast.Msm.commitLagrangeFastWith
          Fast.Msm.defaultWindow urs.w
          (derivedUrsGLagrange urs))).getD column 0 =
        Fast.Msm.commitLagrangeFastWith
          Fast.Msm.defaultWindow urs.w
          (derivedUrsGLagrange urs)
          (top.fixedRows.getD column []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hcolumnRows,
      List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hcolumnRows]
    rfl
  rw [TopLevelCircuit.fixedCommitments, List.parMap_eq_map, hget]
  rw [show LagrangeCommitmentKey.canonical urs top.omega =
      LagrangeCommitmentKey.ofFullList
        urs top.omega (derivedUrsGLagrange urs) hgenerators from
    Subsingleton.elim _ _]
  apply Keygen.commitLagrangeFastWith_eq_ofFullList_commitInstance
    urs top.omega hlen hgenerators
  rw [top.fixedRows_getD_length column hcolumn]
  simp only [TopLevelCircuit.n, hk]

end Halo2.TopLevelCircuit
