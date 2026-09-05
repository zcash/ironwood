import Zcash.Snark.Soundness.Action.AdaptiveStatementModel
import Zcash.Snark.Soundness.AGM.ZeroFamily

/-!
# Non-vacuity of the adaptive-statement Action interface

`ComputedAdaptiveActionStatementFSFamily` is the adversary type the adaptive-statement Action
capstones quantify over. This module constructs an inhabitant for every `ProofParams`: a
zero-query adversary that returns an all-zero statement and proof. It is not claimed to be
accepted; it only rules out vacuous quantification.

The derived Action key has nonzero fixed and permutation commitments, so the generic zero-key
family does not apply. We instead provide each commitment's augmented-basis representation,
including Halo2's default blind `1` on the `w` generator.
-/

namespace Zcash.Snark

open Halo2 Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (Msm derivedUrsGLagrange derivedUrsGLagrange_length omegaOf)

local instance adaptiveInhabitantVestaInhabited : Inhabited VestaG := ⟨0⟩

/-! ## Representations of monomial commitments -/

/-- The AGM point of a monomial commitment carrying an explicit blind on the `w` generator. -/
def algebraicPointOfCommit {k : ℕ} {basis : AugmentedIndex (2 ^ k) → VestaG}
    (coeffs : Fin (2 ^ k) → Fp) (blind : Fp) (P : VestaG)
    (hP : commit (ursOfAugmentedBasis k basis) coeffs +
      blind • (ursOfAugmentedBasis k basis).w = P) :
    AlgebraicPoint (F := Fp) basis where
  point := P
  repr :=
    { coeffs := augmentedCoeffs coeffs ![0, blind]
      hEq := by
        calc
          representationEval basis (augmentedCoeffs coeffs ![0, blind]) =
              representationEval
                (augmentedBasis (ursOfAugmentedBasis k basis).g
                  ![(ursOfAugmentedBasis k basis).u, (ursOfAugmentedBasis k basis).w])
                (augmentedCoeffs coeffs ![0, blind]) :=
            congrArg (fun b => representationEval b (augmentedCoeffs coeffs ![0, blind]))
              (augmentedBasis_ursOfAugmentedBasis k basis).symm
          _ = commitGen (ursOfAugmentedBasis k basis).g coeffs +
                ((0 : Fp) • (ursOfAugmentedBasis k basis).u +
                  blind • (ursOfAugmentedBasis k basis).w) := by
            rw [representationEval_augmentedBasis, Fin.sum_univ_two]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          _ = commit (ursOfAugmentedBasis k basis) coeffs +
                blind • (ursOfAugmentedBasis k basis).w := by
            simp only [zero_smul, zero_add, commit]
            rfl
          _ = P := hP }

@[simp] theorem algebraicPointOfCommit_point {k : ℕ}
    {basis : AugmentedIndex (2 ^ k) → VestaG}
    (coeffs : Fin (2 ^ k) → Fp) (blind : Fp) (P : VestaG)
    (hP : commit (ursOfAugmentedBasis k basis) coeffs +
      blind • (ursOfAugmentedBasis k basis).w = P) :
    (algebraicPointOfCommit coeffs blind P hP).point = P := rfl

/-- The AGM point of the blinding generator itself, which is the commitment of every
public-instance column outside the circuit's configured range. -/
def blindAlgebraicPoint {k : ℕ} (basis : AugmentedIndex (2 ^ k) → VestaG) :
    AlgebraicPoint (F := Fp) basis :=
  algebraicPointOfCommit (basis := basis) (fun _ => 0) 1 (ursOfAugmentedBasis k basis).w (by
    simp [commit])

@[simp] theorem blindAlgebraicPoint_point {k : ℕ}
    (basis : AugmentedIndex (2 ^ k) → VestaG) :
    (blindAlgebraicPoint basis).point = (ursOfAugmentedBasis k basis).w := rfl

/-! ## The derived Action key's verifier-side representations -/

section DerivedKey

variable (pp : ProofParams)
  (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)

/-- The Action circuit's Lagrange-basis fixed-column coherence package at one AGM basis. -/
def adaptiveStatementFixedCoherence :
    TopLevelFixedCoherence actionCircuit
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) :=
  TopLevelFixedCoherence.ofDerived actionCircuit
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    ActionConstraintBounds.domainExponent_lt

/-- Rewrite the derived Lagrange generators into the monomial form used by permutation
commitments. -/
theorem adaptiveStatementLagrangePrefix :
    ∀ i : Fin (2 ^ (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).k),
      (i : ℕ) <
        (derivedUrsGLagrange (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)).length →
      (derivedUrsGLagrange
          (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)).getD (i : ℕ) 0 =
        commit (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
          (polynomialCoefficients
            (2 ^ (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).k)
            (rowPolynomial
              (omegaOf (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).k)
              (Pi.single i (1 : Fp)))) :=
  ofPrefix_setup_of_closed _
    (Nat.le_of_lt_succ ActionConstraintBounds.domainExponent_lt)
    (derivedUrsGLagrange_generator_eq _
      (Nat.le_of_lt_succ ActionConstraintBounds.domainExponent_lt))

/-- The canonical augmented-basis representation of a fixed-column commitment, using the dense
keygen row and Halo2's default blind `1`. -/
def canonicalActionFixedRepresentation (column : Fin actionCircuit.fixedColumnCount) :
    AlgebraicPoint (F := Fp) basis :=
  algebraicPointOfCommit (basis := basis)
    (instanceCoefficients (2 ^ (AdaptiveActionStatementShape pp).k) actionCircuit.omega
      (actionCircuit.fixedRows.getD (column : ℕ) []))
    1
    ((adaptiveActionStatementVk pp basis).fixedCommitment (column : ℕ))
    (by
      have hcoh := adaptiveStatementFixedCoherence pp basis
      calc
        commit (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
              (instanceCoefficients (2 ^ (AdaptiveActionStatementShape pp).k) actionCircuit.omega
                (actionCircuit.fixedRows.getD (column : ℕ) [])) +
              (1 : Fp) • (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w =
            (LagrangeCommitmentKey.canonical
              (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
              actionCircuit.omega).commitInstance
                (actionCircuit.fixedRows.getD (column : ℕ) []) 1 :=
          (LagrangeCommitmentKey.commitInstance_eq _ _ 1).symm
        _ = (actionCircuit.fixedCommitments
              (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)).getD (column : ℕ) 0 :=
          (hcoh (column : ℕ) column.isLt).symm
        _ = (adaptiveActionStatementVk pp basis).fixedCommitment (column : ℕ) :=
          (actionCircuit.toVerifierKey_fixedCommitment _ (column : ℕ)).symm)

@[simp] theorem canonicalActionFixedRepresentation_point
    (column : Fin actionCircuit.fixedColumnCount) :
    (canonicalActionFixedRepresentation pp basis column).point =
      (adaptiveActionStatementVk pp basis).fixedCommitment (column : ℕ) := rfl

/-- The canonical augmented-basis representation of a common-permutation commitment, using its
keygen σ row and the default blind `1`. -/
def canonicalActionPermutationRepresentation
    (c : Fin (AdaptiveActionStatementShape pp).numPermutationColumns) :
    AlgebraicPoint (F := Fp) basis :=
  algebraicPointOfCommit (basis := basis)
    (instanceCoefficients (2 ^ (AdaptiveActionStatementShape pp).k) actionCircuit.omega
      ((permPolysOf (AdaptiveActionStatementShape pp).k actionCircuit.constraintSystem
        actionCircuit.operations).getD (c : ℕ) []))
    1
    ((adaptiveActionStatementVk pp basis).permutationCommonCommitment c)
    (by
      have hc : (c : ℕ) < (permColsOf actionCircuit.constraintSystem).length := by
        have hlen : (permColsOf actionCircuit.constraintSystem).length =
            actionCircuit.permutationColumnCount := by
          simp [permColsOf, TopLevelCircuit.permutationColumnCount,
            TopLevelCircuit.permutationColumns]
        rw [hlen]
        exact c.isLt
      calc
        commit (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
              (instanceCoefficients (2 ^ (AdaptiveActionStatementShape pp).k) actionCircuit.omega
                ((permPolysOf (AdaptiveActionStatementShape pp).k actionCircuit.constraintSystem
                  actionCircuit.operations).getD (c : ℕ) [])) +
              (1 : Fp) • (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w =
            (LagrangeCommitmentKey.ofPrefix
              (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
              (omegaOf (AdaptiveActionStatementShape pp).k)
              (derivedUrsGLagrange
                (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis))
              (adaptiveStatementLagrangePrefix pp basis)).commitInstance
                ((permPolysOf (AdaptiveActionStatementShape pp).k
                  actionCircuit.constraintSystem actionCircuit.operations).getD (c : ℕ) []) 1 :=
          (LagrangeCommitmentKey.commitInstance_eq _ _ 1).symm
        _ = (permutationCommitmentsOf
              (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w
              (derivedUrsGLagrange
                (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis))
              (AdaptiveActionStatementShape pp).k actionCircuit.constraintSystem
              actionCircuit.operations).getD (c : ℕ) 0 :=
          (permutationCommitmentsOf_getD_eq_commitInstance _ _ _
            (derivedUrsGLagrange_length _) (adaptiveStatementLagrangePrefix pp basis)
            (c : ℕ) hc).symm
        _ = (adaptiveActionStatementVk pp basis).permutationCommonCommitment c :=
          (actionCircuit.toVerifierKey_permutationCommonCommitment _ c).symm)

@[simp] theorem canonicalActionPermutationRepresentation_point
    (c : Fin (AdaptiveActionStatementShape pp).numPermutationColumns) :
    (canonicalActionPermutationRepresentation pp basis c).point =
      (adaptiveActionStatementVk pp basis).permutationCommonCommitment c := rfl

/-- The zero adversary's verifier-known representations: zero, the blinding generator, and every
derived fixed-column and common-permutation commitment. -/
def zeroAdaptiveFixedRepresentations : List (AlgebraicPoint (F := Fp) basis) :=
  zeroAlgebraicPoint (shape := AdaptiveActionStatementShape pp) basis ::
    blindAlgebraicPoint basis ::
      (List.ofFn (canonicalActionFixedRepresentation pp basis) ++
        List.ofFn (canonicalActionPermutationRepresentation pp basis))

/-- The source carries the zero point, which represents every commitment of the zero prover. -/
theorem zeroAlgebraicPoint_mem_zeroAdaptiveFixedRepresentations :
    zeroAlgebraicPoint (shape := AdaptiveActionStatementShape pp) basis ∈
      zeroAdaptiveFixedRepresentations pp basis :=
  List.mem_cons_self

/-- The source carries the blinding generator. -/
theorem blindAlgebraicPoint_mem_zeroAdaptiveFixedRepresentations :
    blindAlgebraicPoint basis ∈ zeroAdaptiveFixedRepresentations pp basis :=
  List.mem_cons_of_mem _ List.mem_cons_self

/-- The source carries every fixed-column representation. -/
theorem canonicalActionFixedRepresentation_mem
    (column : Fin actionCircuit.fixedColumnCount) :
    canonicalActionFixedRepresentation pp basis column ∈
      zeroAdaptiveFixedRepresentations pp basis :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_append_left _ (List.mem_ofFn.mpr ⟨column, rfl⟩)))

/-- The source carries every common-permutation representation. -/
theorem canonicalActionPermutationRepresentation_mem
    (c : Fin (AdaptiveActionStatementShape pp).numPermutationColumns) :
    canonicalActionPermutationRepresentation pp basis c ∈
      zeroAdaptiveFixedRepresentations pp basis :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_append_right _ (List.mem_ofFn.mpr ⟨c, rfl⟩)))

/-- Every fixed-column commitment the derived key's query layout names is represented. -/
theorem zeroAdaptiveFixedRepresentations_fixedRepresented (i : ℕ)
    (hi : ∃ rotation, (i, rotation) ∈ (adaptiveActionStatementVk pp basis).fixedQueryLayout) :
    ∃ ap ∈ zeroAdaptiveFixedRepresentations pp basis,
      ap.point = (adaptiveActionStatementVk pp basis).fixedCommitment i := by
  obtain ⟨rotation, hmem⟩ := hi
  rw [actionCircuit.toVerifierKey_fixedQueryLayout] at hmem
  have hlt : i < actionCircuit.fixedColumnCount :=
    List.forall_iff_forall_mem.mp
      actionCircuit.fixedQueryLayout_columns_lt (i, rotation) hmem
  exact ⟨canonicalActionFixedRepresentation pp basis ⟨i, hlt⟩,
    canonicalActionFixedRepresentation_mem pp basis ⟨i, hlt⟩, rfl⟩

/-- Every common-permutation commitment of the derived key is represented. -/
theorem zeroAdaptiveFixedRepresentations_permutationCommonRepresented
    (c : Fin (AdaptiveActionStatementShape pp).numPermutationColumns) :
    ∃ ap ∈ zeroAdaptiveFixedRepresentations pp basis,
      ap.point = (adaptiveActionStatementVk pp basis).permutationCommonCommitment c :=
  ⟨canonicalActionPermutationRepresentation pp basis c,
    canonicalActionPermutationRepresentation_mem pp basis c, rfl⟩

end DerivedKey

/-! ## Coverage of the assembled multiopen data by a representation source

These lemmas generalize `MsmZeroData` from zero commitments to commitments represented by a
source, as required by a nonzero verifying key.
-/

section Coverage

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
  {source : List (AlgebraicPoint (F := Fp) basis)}

/-- Every nongenerator point in the MSM has a representation in `source`. -/
def MsmCovered (source : List (AlgebraicPoint (F := Fp) basis))
    (m : Msm shape.k Fp VestaG) : Prop :=
  ∀ t ∈ m.other, ∃ ap ∈ source, ap.point = t.2

theorem msmCovered_zero : MsmCovered source (Msm.zero shape.k Fp VestaG) :=
  fun _t ht => absurd ht List.not_mem_nil

theorem msmCovered_appendTerm {m : Msm shape.k Fp VestaG} (hm : MsmCovered source m)
    {P : VestaG} (hP : ∃ ap ∈ source, ap.point = P) (c : Fp) :
    MsmCovered source (m.appendTerm c P) := by
  intro t ht
  rcases List.mem_cons.mp ht with h0 | hmem
  · rw [h0]
    exact hP
  · exact hm t hmem

theorem msmCovered_scale {m : Msm shape.k Fp VestaG} (hm : MsmCovered source m) (c : Fp) :
    MsmCovered source (m.scale c) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hm s hs

theorem msmCovered_add {m₁ m₂ : Msm shape.k Fp VestaG}
    (h₁ : MsmCovered source m₁) (h₂ : MsmCovered source m₂) :
    MsmCovered source (m₁.add m₂) := by
  intro t ht
  rcases List.mem_append.mp ht with hmem | hmem
  · exact h₁ t hmem
  · exact h₂ t hmem

/-- Coverage only grows with the representation source. -/
theorem commitmentRefCovered_mono {source' : List (AlgebraicPoint (F := Fp) basis)}
    (hsub : source ⊆ source') {c : CommitmentRef shape.k Fp VestaG}
    (hc : CommitmentRefCovered source c) : CommitmentRefCovered source' c := by
  cases c with
  | point P =>
      obtain ⟨ap, hap, hpoint⟩ := hc
      exact ⟨ap, hsub hap, hpoint⟩
  | msm m =>
      intro pr hpr
      obtain ⟨ap, hap, hpoint⟩ := hc pr hpr
      exact ⟨ap, hsub hap, hpoint⟩

/-- Accumulating a covered reference into a covered MSM stays covered. -/
theorem commitmentRefCovered_accumulate {c : CommitmentRef shape.k Fp VestaG}
    (hc : CommitmentRefCovered source c) {acc : Msm shape.k Fp VestaG}
    (hacc : MsmCovered source acc) (pow : Fp) :
    MsmCovered source (accumulateCommitment pow c acc) := by
  cases c with
  | point P => exact msmCovered_appendTerm hacc hc pow
  | msm m => exact msmCovered_add hacc (msmCovered_scale hc pow)

/-- The folded vanishing-`h` MSM is covered once every quotient piece is. -/
theorem msmCovered_vanishingHCommitment (xn : Fp) (hPieces : List VestaG)
    (hcov : ∀ P ∈ hPieces, ∃ ap ∈ source, ap.point = P) :
    MsmCovered source (vanishingHCommitment shape.k xn hPieces) := by
  unfold vanishingHCommitment
  have hgen : ∀ (l : List VestaG), (∀ P ∈ l, ∃ ap ∈ source, ap.point = P) →
      ∀ acc : Msm shape.k Fp VestaG, MsmCovered source acc →
      MsmCovered source (l.foldl (fun acc c => (acc.scale xn).appendTerm (1 : Fp) c) acc) := by
    intro l
    induction l with
    | nil => exact fun _ _acc h => h
    | cons P l ih =>
        intro hl acc hacc
        rw [List.foldl_cons]
        exact ih (fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)) _
          (msmCovered_appendTerm (msmCovered_scale hacc xn) (hl P List.mem_cons_self) 1)
  exact hgen _ (fun P hP => hcov P (List.mem_reverse.mp hP)) _ msmCovered_zero

/-- Compressing a point set whose references are covered yields a covered MSM. -/
theorem compressSet_fst_covered (x1 : Fp)
    (setQueries : List (CommitmentRef shape.k Fp VestaG × List Fp)) (numPoints : ℕ)
    (hcov : ∀ qc ∈ setQueries, CommitmentRefCovered source qc.1) :
    MsmCovered source (compressSet x1 setQueries numPoints).1 := by
  unfold compressSet
  have hgen : ∀ l : List (CommitmentRef shape.k Fp VestaG × List Fp),
      (∀ qc ∈ l, CommitmentRefCovered source qc.1) →
      ∀ st : Msm shape.k Fp VestaG × List Fp × Fp, MsmCovered source st.1 →
      MsmCovered source (l.foldl (fun (st : Msm shape.k Fp VestaG × List Fp × Fp) qc =>
        (accumulateCommitment st.2.2 qc.1 st.1,
         (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
         st.2.2 * x1)) st).1 := by
    intro l
    induction l with
    | nil => exact fun _ _st h => h
    | cons qc l ih =>
        intro hl st hst
        rw [List.foldl_cons]
        exact ih (fun qc' hqc' => hl qc' (List.mem_cons_of_mem _ hqc')) _
          (commitmentRefCovered_accumulate (hl qc List.mem_cons_self) hst st.2.2)
  exact hgen _ hcov _ msmCovered_zero

/-- The `x₄` collapse of covered compressed commitments against a covered `q′` stays covered. -/
theorem multiopenCombine_fst_covered (x4 : Fp) {qPrime : VestaG}
    (hqPrime : ∃ ap ∈ source, ap.point = qPrime)
    (qCommitments : List (Msm shape.k Fp VestaG)) (u : List Fp) (msmEval : Fp)
    (hcov : ∀ m ∈ qCommitments, MsmCovered source m) :
    MsmCovered source
      (multiopenCombine x4 qPrime qCommitments u msmEval (Msm.zero shape.k Fp VestaG)).1 := by
  unfold multiopenCombine
  have hgen : ∀ l : List (Msm shape.k Fp VestaG × Fp),
      (∀ p ∈ l, MsmCovered source p.1) → ∀ st : Msm shape.k Fp VestaG × Fp,
      MsmCovered source st.1 →
      MsmCovered source (l.foldl (fun (st : Msm shape.k Fp VestaG × Fp) p =>
        ((st.1.scale x4).add p.1, st.2 * x4 + p.2)) st).1 := by
    intro l
    induction l with
    | nil => exact fun _ _st h => h
    | cons p l ih =>
        intro hl st hst
        rw [List.foldl_cons]
        exact ih (fun p' hp' => hl p' (List.mem_cons_of_mem _ hp')) _
          (msmCovered_add (msmCovered_scale hst x4) (hl p List.mem_cons_self))
  refine hgen _ ?_ _ ?_
  · intro p hp
    exact hcov p.1 (List.of_mem_zip hp).1
  · exact msmCovered_appendTerm msmCovered_zero hqPrime 1

/-- Column queries are covered once the source represents every commitment the layout names. -/
theorem columnQueries_covered (omega x : Fp) (commitment : ℕ → VestaG)
    (mkId : ℕ → CommitmentId) (layout : List (ℕ × ℤ)) (evals : List Fp)
    (hcomm : ∀ e ∈ layout, ∃ ap ∈ source, ap.point = commitment e.1) :
    ∀ q ∈ columnQueries (k := shape.k) omega x commitment mkId layout evals,
      CommitmentRefCovered source q.commitment := by
  intro q hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
  exact hcomm e.1 (List.of_mem_zip he).1

/-- Every query from the zero proof string is covered when the source represents zero, instance,
fixed-column, and common-permutation commitments. -/
theorem assembleQueries_covered_zeroProofString
    (vk : VerifyingKey shape Fp VestaG) (ic : Fin shape.numProofs → ℕ → VestaG)
    (hzero : ∃ ap ∈ source, ap.point = (0 : VestaG))
    (hic : ∀ p i, ∃ ap ∈ source, ap.point = ic p i)
    (hfixed : ∀ i rotation, (i, rotation) ∈ vk.fixedQueryLayout →
      ∃ ap ∈ source, ap.point = vk.fixedCommitment i)
    (hperm : ∀ c, ∃ ap ∈ source, ap.point = vk.permutationCommonCommitment c)
    (ch : Challenges shape.k Fp) :
    ∀ q ∈ assembleQueries vk ic (zeroProofString shape Fp VestaG) ch,
      CommitmentRefCovered source q.commitment := by
  have hzeroOf : ∀ {P : VestaG}, P = 0 → ∃ ap ∈ source, ap.point = P := by
    intro P hP
    rw [hP]
    exact hzero
  intro q hq
  simp only [assembleQueries] at hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · -- per-proof queries
        obtain ⟨lqs, hlqs, hqmem⟩ := List.mem_flatten.mp hq
        obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hlqs
        rcases List.mem_append.mp hqmem with hqm | hqm
        · rcases List.mem_append.mp hqm with hqm | hqm
          · rcases List.mem_append.mp hqm with hqm | hqm
            · -- instance-column queries
              exact columnQueries_covered _ _ _ _ _ _ (fun e _ => hic p e.1) q hqm
            · -- advice-column queries through `finFnG`
              exact columnQueries_covered _ _ _ _ _ _
                (fun e _ => hzeroOf (finFnG_zero rfl e.1)) q hqm
          · -- permutation product queries
            rcases List.mem_append.mp hqm with hqm | hqm
            · obtain ⟨s, hs, hqm⟩ := List.mem_flatMap.mp hqm
              obtain ⟨hzip, -⟩ := List.of_mem_zip hs
              obtain ⟨j, hj⟩ := List.mem_ofFn.mp hzip
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hqm
              rcases hqm with h0 | h0 <;>
                (rw [h0]
                 exact hzeroOf (show s.1.1 = 0 by rw [← hj]; rfl))
            · obtain ⟨s, hs, hsome⟩ := List.mem_filterMap.mp hqm
              have hsmem := List.mem_reverse.mp (List.mem_of_mem_drop hs)
              obtain ⟨hzip, -⟩ := List.of_mem_zip hsmem
              obtain ⟨j, hj⟩ := List.mem_ofFn.mp hzip
              obtain ⟨le, -, hqe⟩ := Option.map_eq_some_iff.mp hsome
              rw [← hqe]
              exact hzeroOf (show s.1.1 = 0 by rw [← hj]; rfl)
        · -- lookup queries
          obtain ⟨l, hl, hqm⟩ := List.mem_flatMap.mp hqm
          obtain ⟨hlmem, -⟩ := List.of_mem_zip hl
          obtain ⟨j, hj⟩ := List.mem_ofFn.mp hlmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hqm
          rcases hqm with h0 | h0 | h0 | h0 | h0 <;>
            first
            | (rw [h0]; exact hzeroOf (show l.1.1.product = 0 by rw [← hj]; rfl))
            | (rw [h0]; exact hzeroOf (show l.1.1.permutedInput = 0 by rw [← hj]; rfl))
            | (rw [h0]; exact hzeroOf (show l.1.1.permutedTable = 0 by rw [← hj]; rfl))
      · -- fixed-column queries
        exact columnQueries_covered _ _ _ _ _ _
          (fun e he => hfixed e.1 e.2 he) q hq
    · -- common permutation queries
      obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hq
      obtain ⟨hmem, -⟩ := List.of_mem_zip hce
      obtain ⟨c, hc⟩ := List.mem_ofFn.mp hmem
      show ∃ ap ∈ source, ap.point = ce.1.1
      rw [← hc]
      exact hperm c
  · -- vanishing queries
    rcases List.mem_cons.mp hq with h0 | hq
    · rw [h0]
      refine msmCovered_vanishingHCommitment _ _ ?_
      intro P hP
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
      exact hzero
    · rcases List.mem_cons.mp hq with h0 | hq
      · rw [h0]
        exact hzero
      · exact absurd hq List.not_mem_nil

/-- Every reference routed to a deployed point set comes from an assembled query and is covered. -/
theorem deployedSetQueries_covered
    (vk : VerifyingKey shape Fp VestaG) (ic : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (hqueries : ∀ q ∈ assembleQueries vk ic ps ch, CommitmentRefCovered source q.commitment)
    (i : ℕ) :
    ∀ qc ∈ deployedSetQueries vk ic ps ch i, CommitmentRefCovered source qc.1 := by
  intro qc hqc
  unfold deployedSetQueries at hqc
  set grouped := constructIntermediateSets (assembleQueries vk ic ps ch) with hgrouped
  by_cases hi : i < (grouped.sets.zip grouped.points).length
  · rw [List.getD_eq_getElem _ _ hi] at hqc
    have hset : (grouped.sets.zip grouped.points)[i].1 ∈ grouped.sets := by
      rw [List.getElem_zip]
      exact List.getElem_mem _
    obtain ⟨q, hq, hEq⟩ := constructIntermediateSets_sets_ref_provenance _ hset hqc
    rw [hEq]
    exact hqueries q hq
  · rw [List.getD_eq_default _ _ (le_of_not_gt hi)] at hqc
    exact absurd hqc List.not_mem_nil

/-- The assembled multiopen MSM is covered once every assembled query and the prover's `q′` are. -/
theorem multiopenMsm_covered
    (vk : VerifyingKey shape Fp VestaG) (ic : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (hqPrime : ∃ ap ∈ source, ap.point = ps.multiopenQPrime)
    (hqueries : ∀ q ∈ assembleQueries vk ic ps ch, CommitmentRefCovered source q.commitment) :
    MsmCovered source (multiopenMsm vk ic ps ch) := by
  unfold multiopenMsm assembleOpening
  refine multiopenCombine_fst_covered _ hqPrime _ _ _ ?_
  intro m hm
  obtain ⟨msm, hmsm, rfl⟩ := List.mem_map.mp hm
  obtain ⟨sp, hsp, rfl⟩ := List.mem_map.mp hmsm
  refine compressSet_fst_covered _ _ _ ?_
  intro qc hqc
  obtain ⟨q, hq, hEq⟩ := constructIntermediateSets_sets_ref_provenance _
    (List.of_mem_zip hsp).1 hqc
  rw [hEq]
  exact hqueries q hq

end Coverage

/-! ## The zero adaptive-statement adversary -/

/-- The all-zero Action public input. -/
def zeroActionPublicInputs : PublicInputs Fp :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

section Adversary

variable (pp : ProofParams)
  (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)

/-- The all-zero public statement of the smoke-test adversary. -/
def zeroAdaptiveInputs : Fin pp.numProofs → PublicInputs Fp :=
  fun _ => zeroActionPublicInputs

/-- The zero adversary's instance and verifier-known key representations. -/
def zeroAdaptiveSource : List (AlgebraicPoint (F := Fp) basis) :=
  adaptiveStatementInstanceRepresentationList
    (canonicalAdaptiveStatementInstanceRepresentation pp basis (zeroAdaptiveInputs pp)) ++
    zeroAdaptiveFixedRepresentations pp basis

/-- The verifier-known representations are part of the proof data's coverage source. -/
theorem mem_zeroAdaptiveSource_of_mem_fixed
    {ap : AlgebraicPoint (F := Fp) basis}
    (hap : ap ∈ zeroAdaptiveFixedRepresentations pp basis) :
    ap ∈ zeroAdaptiveSource pp basis :=
  List.mem_append_right _ hap

/-- The zero point is represented in the source. -/
theorem zeroAdaptiveSource_zero :
    ∃ ap ∈ zeroAdaptiveSource pp basis, ap.point = (0 : VestaG) :=
  ⟨zeroAlgebraicPoint (shape := AdaptiveActionStatementShape pp) basis,
    mem_zeroAdaptiveSource_of_mem_fixed pp basis
      (zeroAlgebraicPoint_mem_zeroAdaptiveFixedRepresentations pp basis), rfl⟩

/-- Every statement-derived instance commitment is represented: configured columns canonically,
and remaining columns by the blinding generator. -/
theorem zeroAdaptiveSource_instance
    (p : Fin (AdaptiveActionStatementShape pp).numProofs) (column : ℕ) :
    ∃ ap ∈ zeroAdaptiveSource pp basis,
      ap.point =
        adaptiveActionStatementInstanceCommitment pp basis (zeroAdaptiveInputs pp) p column := by
  by_cases hcolumn : column < (AdaptiveActionStatementShape pp).numInstanceColumns
  · refine ⟨canonicalAdaptiveStatementInstanceRepresentation pp basis (zeroAdaptiveInputs pp) p
      ⟨column, hcolumn⟩, ?_, rfl⟩
    refine List.mem_append_left _ ?_
    rw [adaptiveStatementInstanceRepresentationList]
    refine List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, ?_⟩
    exact List.mem_ofFn.mpr ⟨⟨column, hcolumn⟩, rfl⟩
  · have hbound := congrFun (congrFun
      (adaptiveActionStatementInstanceCommitment_eq_bounded pp basis (zeroAdaptiveInputs pp)) p)
      column
    rw [boundedAdaptiveStatementInstanceCommitment, if_neg hcolumn] at hbound
    exact ⟨blindAlgebraicPoint basis,
      mem_zeroAdaptiveSource_of_mem_fixed pp basis
        (blindAlgebraicPoint_mem_zeroAdaptiveFixedRepresentations pp basis), hbound.symm⟩

/-- Every query the deployed verifier assembles from the zero proof string is covered. -/
theorem zeroAdaptiveSource_assembleQueries (ch : Challenges (AdaptiveActionStatementShape pp).k Fp) :
    ∀ q ∈ assembleQueries (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis (zeroAdaptiveInputs pp))
        (zeroProofString (AdaptiveActionStatementShape pp) Fp VestaG) ch,
      CommitmentRefCovered (zeroAdaptiveSource pp basis) q.commitment :=
  assembleQueries_covered_zeroProofString _ _
    (zeroAdaptiveSource_zero pp basis)
    (zeroAdaptiveSource_instance pp basis)
    (fun i rotation hmem => by
      obtain ⟨ap, hap, hpoint⟩ :=
        zeroAdaptiveFixedRepresentations_fixedRepresented pp basis i ⟨rotation, hmem⟩
      exact ⟨ap, mem_zeroAdaptiveSource_of_mem_fixed pp basis hap, hpoint⟩)
    (fun c => by
      obtain ⟨ap, hap, hpoint⟩ :=
        zeroAdaptiveFixedRepresentations_permutationCommonRepresented pp basis c
      exact ⟨ap, mem_zeroAdaptiveSource_of_mem_fixed pp basis hap, hpoint⟩)
    ch

/-- All-zero proof data whose assembled and routed commitments have canonical representations. -/
def zeroAdaptiveProofData :
    OnlineMemberProofData
      (vk := adaptiveActionStatementVk pp basis)
      (instanceCommitment :=
        adaptiveActionStatementInstanceCommitment pp basis (zeroAdaptiveInputs pp))
      basis (zeroAdaptiveSource pp basis) where
  algebraicProof := zeroAlgebraicProofString (shape := AdaptiveActionStatementShape pp) basis
  wellFormed := zeroProofString_wellFormed
  assemblyCovered := by
    intro nu pr hpr
    obtain ⟨ap, hap, hpoint⟩ :=
      multiopenMsm_covered (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis (zeroAdaptiveInputs pp))
        (zeroAlgebraicProofString (shape := AdaptiveActionStatementShape pp) basis).erase
        (chRecord nu (fun _ => 0))
        (zeroAdaptiveSource_zero pp basis)
        (zeroAdaptiveSource_assembleQueries pp basis (chRecord nu (fun _ => 0))) pr hpr
    exact ⟨ap, List.mem_append_left _ (List.mem_append_right _ hap), hpoint⟩
  membersCovered := by
    intro nu i _hi m
    have hmem : (deployedSetQueries (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis (zeroAdaptiveInputs pp))
          (zeroAlgebraicProofString (shape := AdaptiveActionStatementShape pp) basis).erase
          (chRecord nu (fun _ => 0)) i).getD (m : ℕ) (.point 0, []) ∈
        deployedSetQueries (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis (zeroAdaptiveInputs pp))
          (zeroAlgebraicProofString (shape := AdaptiveActionStatementShape pp) basis).erase
          (chRecord nu (fun _ => 0)) i := by
      rw [List.getD_eq_getElem _ _ m.isLt]
      exact List.getElem_mem _
    exact commitmentRefCovered_mono (by intro a ha; exact List.mem_append_right _ ha)
      (deployedSetQueries_covered _ _ _ _
        (zeroAdaptiveSource_assembleQueries pp basis (chRecord nu (fun _ => 0))) i _ hmem)

/-- The zero adversary's statement and proof output. -/
def zeroAdaptiveStatementOutput :
    AdaptiveActionStatementOutput pp basis (zeroAdaptiveFixedRepresentations pp basis) where
  inputs := zeroAdaptiveInputs pp
  instanceRepresentations :=
    canonicalAdaptiveStatementInstanceRepresentation pp basis (zeroAdaptiveInputs pp)
  instanceRepresented := fun _ _ => rfl
  proofData := zeroAdaptiveProofData pp basis

end Adversary

/-- The zero family's representation table holds the zero point, the blinding generator, and one
entry per fixed and common-permutation column. Generic selector compression and configured-column
bounds put its length at most 97, far inside the `2^89` interface cap. Discharging the invariant
concretely is what stops the capstones' quantifier from ranging over a class no family is known to
satisfy. -/
theorem zeroAdaptiveFixedRepresentations_length_le (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :
    (zeroAdaptiveFixedRepresentations pp basis).length ≤
      adaptiveStatementFixedRepresentationLimit := by
  simp only [zeroAdaptiveFixedRepresentations, List.length_cons, List.length_append,
    List.length_ofFn, AdaptiveActionStatementShape,
    CircuitShape.withProofParams_numPermutationColumns,
    adaptiveStatementFixedRepresentationLimit]
  rw [Halo2.TopLevelCircuit.shape_numPermutationColumns]
  have hfixed : actionCircuit.fixedColumnCount ≤ 70 := by
    calc
      actionCircuit.fixedColumnCount ≤
          actionCircuit.constraintSystem.numFixedColumns +
            actionCircuit.selectorCount :=
        actionCircuit.fixedColumnCount_le_numFixedColumns_add_selectorCount
      _ = 14 + 56 := by
        rw [actionCircuit_numFixedColumns_eq,
          actionCircuit_selectorCount_eq]
      _ = 70 := by norm_num
  have hpermutation : actionCircuit.permutationColumnCount ≤ 25 := by
    simpa only [actionCircuit_numAdviceColumns_eq,
      actionCircuit_numFixedColumns_eq,
      actionCircuit_numInstanceColumns_eq] using
        actionCircuit.permutationColumnCount_le_configuredColumnCount
  calc
    actionCircuit.fixedColumnCount +
        actionCircuit.permutationColumnCount + 1 + 1 ≤
      70 + 25 + 1 + 1 := by omega
    _ ≤ 2 ^ 89 := by norm_num

/-- A zero-query family that returns an all-zero statement and proof and represents every
derived-key commitment. It inhabits the interface but is not claimed to be accepted. -/
def zeroAdaptiveStatementFamily (pp : ProofParams) :
    ComputedAdaptiveActionStatementFSFamily pp where
  vkHash := fun _ _ => 0
  fixedRepresentations := zeroAdaptiveFixedRepresentations pp
  fixedRepresentations_length_le := zeroAdaptiveFixedRepresentations_length_le pp
  fixedRepresented := zeroAdaptiveFixedRepresentations_fixedRepresented pp
  permutationCommonRepresented := zeroAdaptiveFixedRepresentations_permutationCommonRepresented pp
  adversary := fun basis => .pure (zeroAdaptiveStatementOutput pp basis)
  Q := 0
  queryBound := fun _ => .pure _ 0

/-- The adaptive-statement adversary interface is inhabited for every proof parameterization. -/
theorem adaptiveStatementInterface_nonempty (pp : ProofParams) :
    Nonempty (ComputedAdaptiveActionStatementFSFamily pp) :=
  ⟨zeroAdaptiveStatementFamily pp⟩

end Zcash.Snark
