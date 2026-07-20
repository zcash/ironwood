import Zcash.Security.BindingSignature.Orchard
import Zcash.Security.BindingSignature.Sapling
import Zcash.Snark.Soundness.AGM.Adapter

/-!
# Binding-signature relations as AGM inputs

The binding-signature reduction computes `NontrivialRelation V R`. This module converts it to the
generic AGM relation type and, when `R ≠ 0`, computes the discrete log of `V` base `R`. The Orchard
and Sapling endpoints include their integer range and no-overflow checks. All relations remain
explicit data.
-/

namespace Zcash.Security.BindingSignature

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- The two public bases used by the binding-signature relation. -/
def bindingSignatureBasis (V R : M) : Fin 2 → M
  | 0 => V
  | 1 => R

/-- The two coefficients of a binding-signature relation. -/
def bindingSignatureCoeffs (α β : F) : Fin 2 → F
  | 0 => α
  | 1 => β

theorem representationEval_bindingSignatureBasis (V R : M) (α β : F) :
    Zcash.Snark.representationEval (bindingSignatureBasis V R) (bindingSignatureCoeffs α β)
      = α • V + β • R := by
  simp [Zcash.Snark.representationEval, bindingSignatureBasis, bindingSignatureCoeffs,
    Fin.sum_univ_two]

/-- Convert a binding-signature relation to the generic AGM relation type. -/
def NontrivialRelation.toAlgebraicRelationWitness (V R : M)
    (r : NontrivialRelation (F := F) V R) :
    Zcash.Snark.AlgebraicRelationWitness (F := F) (bindingSignatureBasis V R) :=
  { coeffs := bindingSignatureCoeffs r.α r.β
    nontrivial := by
      intro hzero
      have hα : r.α = 0 := by
        have h := congrFun hzero 0
        simpa [bindingSignatureCoeffs] using h
      have hβ : r.β = 0 := by
        have h := congrFun hzero 1
        simpa [bindingSignatureCoeffs] using h
      rcases r.nontrivial with ha | hαβ
      · exact ha (Subsingleton.elim _ _)
      · rcases hαβ with hα' | hβ'
        · exact hα' hα
        · exact hβ' hβ
    relation := by
      rw [representationEval_bindingSignatureBasis]
      simpa [Zcash.Snark.commitGen] using r.relation }

/-- Compute the discrete log of `V` base `R` from a two-base relation, assuming `R ≠ 0`. -/
def NontrivialRelation.toDiscreteLog [DecidableEq F] (V R : M)
    (r : NontrivialRelation (F := F) V R)
    (hR : R ≠ 0) : Zcash.Snark.DiscreteLogRepresentation (F := F) R V := by
  by_cases hα : r.α = 0
  · exfalso
    have hβ : r.β ≠ 0 := by
      rcases r.nontrivial with ha | hαβ
      · exact False.elim (ha (Subsingleton.elim _ _))
      · rcases hαβ with hα' | hβ'
        · exact False.elim (hα' hα)
        · exact hβ'
    have hβR : r.β • R = 0 := by
      simpa [Zcash.Snark.commitGen, hα] using r.relation
    have hR0 : R = 0 := by
      have h := congrArg (fun X : M => r.β⁻¹ • X) hβR
      simpa [smul_smul, inv_mul_cancel₀ hβ] using h
    exact hR hR0
  · exact Zcash.Snark.discreteLogOfU_of_augmentedRelation R (Fin.elim0 : Fin 0 → M) V R
      Fin.elim0 1 r (fun i => Fin.elim0 i) (by simp) hα

/-- Turn a verifying, range-bounded Orchard imbalance into the discrete log of `V` base `R`. -/
def orchardImbalanceToDiscreteLog {M : Type*} [AddCommGroup M]
    [Module (ZMod pallasScalarOrder) M]
    (V R : M) (actions : List (ℤ × ZMod pallasScalarOrder)) (vBalance : ℤ)
    (bsk : ZMod pallasScalarOrder)
    (hne : (actions.map Prod.fst).sum - vBalance ≠ 0)
    (hv : ∀ v ∈ actions.map Prod.fst, |v| ≤ 2^64 - 1)
    (hn : actions.length ≤ 2^16 - 1)
    (hvBalance : |vBalance| ≤ 2^63)
    (hExtract : bindingVK V R (castBundle actions) (castBundle [])
      (vBalance : ZMod pallasScalarOrder) = bsk • R)
    (hR : R ≠ 0) :
    Zcash.Snark.DiscreteLogRepresentation (F := ZMod pallasScalarOrder) R V :=
  (NontrivialRelation.ofOrchardImbalance V R actions vBalance bsk hne hv hn hvBalance
    hExtract).toDiscreteLog V R hR

/-- Turn a verifying, range-bounded Sapling imbalance into the discrete log of `V` base `R`. -/
def saplingImbalanceToDiscreteLog {M : Type*} [AddCommGroup M]
    [Module (ZMod jubjubScalarOrder) M]
    (V R : M) (spends outputs : List (ℤ × ZMod jubjubScalarOrder)) (vBalance : ℤ)
    (bsk : ZMod jubjubScalarOrder)
    (hne : (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance ≠ 0)
    (hOld : ∀ v ∈ spends.map Prod.fst, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hNew : ∀ v ∈ outputs.map Prod.fst, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hnOld : spends.length ≤ saplingMaxSpends)
    (hnNew : outputs.length ≤ saplingMaxOutputs)
    (hvBalance : |vBalance| ≤ 2^63)
    (hExtract : bindingVK V R (castBundle spends) (castBundle outputs)
      (vBalance : ZMod jubjubScalarOrder) = bsk • R)
    (hR : R ≠ 0) :
    Zcash.Snark.DiscreteLogRepresentation (F := ZMod jubjubScalarOrder) R V :=
  (NontrivialRelation.ofSaplingImbalance V R spends outputs vBalance bsk hne hOld hNew
    hnOld hnNew hvBalance hExtract).toDiscreteLog V R hR

end Zcash.Security.BindingSignature
