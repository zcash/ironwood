import Zcash.Common.AlgebraicRelation
import Zcash.Security.BindingSignature.Orchard
import Zcash.Security.BindingSignature.Sapling

/-!
# Binding-signature relations as discrete logs

The binding-signature reduction computes `NontrivialRelation Vbase Rbase`. This module converts it
to the generic relation type over a two-element basis and, when `Rbase ≠ 0`, computes the discrete
log of `Vbase` base `Rbase`. The Orchard and Sapling endpoints include their integer range and
no-overflow checks. All relations remain explicit data.

Nothing here restricts the adversary: the input is relation coefficients, whoever produced them,
and the output is a field solve. What scopes the conclusion is the sampling of `Vbase` and `Rbase`
as an unpredictable reference string, not an algebraic-prover assumption.
-/

namespace Zcash.Security.BindingSignature

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- The two public bases used by the binding-signature relation. -/
def bindingSignatureBasis (Vbase Rbase : M) : Fin 2 → M
  | 0 => Vbase
  | 1 => Rbase

/-- The two coefficients of a binding-signature relation. -/
def bindingSignatureCoeffs (α β : F) : Fin 2 → F
  | 0 => α
  | 1 => β

theorem representationEval_bindingSignatureBasis (Vbase Rbase : M) (α β : F) :
    representationEval (bindingSignatureBasis Vbase Rbase) (bindingSignatureCoeffs α β)
      = α • Vbase + β • Rbase := by
  simp [representationEval, bindingSignatureBasis, bindingSignatureCoeffs, Fin.sum_univ_two]

/-- Convert a binding-signature relation to the generic relation type over a public basis. -/
def NontrivialRelation.toAlgebraicRelationWitness (Vbase Rbase : M)
    (r : NontrivialRelation (F := F) Vbase Rbase) :
    AlgebraicRelationWitness (F := F) (bindingSignatureBasis Vbase Rbase) :=
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
      simpa [Zcash.commitGen] using r.relation }

/-- Compute the discrete log of `Vbase` base `Rbase` from a two-base relation, assuming `Rbase ≠ 0`. -/
def NontrivialRelation.toDiscreteLog [DecidableEq F] (Vbase Rbase : M)
    (r : NontrivialRelation (F := F) Vbase Rbase)
    (hR : Rbase ≠ 0) : DiscreteLogWitness (F := F) Rbase Vbase := by
  by_cases hα : r.α = 0
  · exfalso
    have hβ : r.β ≠ 0 := by
      rcases r.nontrivial with ha | hαβ
      · exact False.elim (ha (Subsingleton.elim _ _))
      · rcases hαβ with hα' | hβ'
        · exact False.elim (hα' hα)
        · exact hβ'
    have hβR : r.β • Rbase = 0 := by
      simpa [commitGen, hα] using r.relation
    have hR0 : Rbase = 0 := by
      have h := congrArg (fun X : M => r.β⁻¹ • X) hβR
      simpa [smul_smul, inv_mul_cancel₀ hβ] using h
    exact hR hR0
  · exact discreteLogOfU_of_augmentedRelation Rbase (Fin.elim0 : Fin 0 → M) Vbase Rbase
      Fin.elim0 1 r (fun i => Fin.elim0 i) (by simp) hα

/-- Turn a verifying, range-bounded Orchard imbalance into the discrete log of `Vbase` base `Rbase`. -/
def orchardImbalanceToDiscreteLog {M : Type*} [AddCommGroup M]
    [Module (ZMod pallasScalarOrder) M]
    (Vbase Rbase : M) (actions : List (ℤ × ZMod pallasScalarOrder)) (vBalance : ℤ)
    (bsk : ZMod pallasScalarOrder)
    (hne : (actions.map Prod.fst).sum - vBalance ≠ 0)
    (hv : ∀ v ∈ actions.map Prod.fst, |v| ≤ 2^64 - 1)
    (hn : actions.length ≤ 2^16 - 1)
    (hvBalance : |vBalance| ≤ 2^63)
    (hExtract : bindingVK Vbase Rbase (castBundle actions) (castBundle [])
      (vBalance : ZMod pallasScalarOrder) = bsk • Rbase)
    (hR : Rbase ≠ 0) :
    DiscreteLogWitness (F := ZMod pallasScalarOrder) Rbase Vbase :=
  (NontrivialRelation.ofOrchardImbalance Vbase Rbase actions vBalance bsk hne hv hn hvBalance
    hExtract).toDiscreteLog Vbase Rbase hR

/-- Turn a verifying, range-bounded Sapling imbalance into the discrete log of `Vbase` base `Rbase`. -/
def saplingImbalanceToDiscreteLog {M : Type*} [AddCommGroup M]
    [Module (ZMod jubjubScalarOrder) M]
    (Vbase Rbase : M) (spends outputs : List (ℤ × ZMod jubjubScalarOrder)) (vBalance : ℤ)
    (bsk : ZMod jubjubScalarOrder)
    (hne : (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance ≠ 0)
    (hOld : ∀ v ∈ spends.map Prod.fst, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hNew : ∀ v ∈ outputs.map Prod.fst, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hnOld : spends.length ≤ saplingMaxSpends)
    (hnNew : outputs.length ≤ saplingMaxOutputs)
    (hvBalance : |vBalance| ≤ 2^63)
    (hExtract : bindingVK Vbase Rbase (castBundle spends) (castBundle outputs)
      (vBalance : ZMod jubjubScalarOrder) = bsk • Rbase)
    (hR : Rbase ≠ 0) :
    DiscreteLogWitness (F := ZMod jubjubScalarOrder) Rbase Vbase :=
  (NontrivialRelation.ofSaplingImbalance Vbase Rbase spends outputs vBalance bsk hne hOld hNew
    hnOld hnNew hvBalance hExtract).toDiscreteLog Vbase Rbase hR

end Zcash.Security.BindingSignature
