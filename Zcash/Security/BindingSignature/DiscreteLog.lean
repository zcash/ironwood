import Zcash.Common.DiscreteLogRelation
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

/-- Convert a binding-signature relation to the generic relation type over a basis that
carries `Vbase` and `Rbase` at two distinct slots. The relation's coefficients are placed at
those slots and vanish elsewhere. -/
def NontrivialRelation.toAlgebraicRelationWitnessAt {m : ℕ} {Vbase Rbase : M}
    (rel : NontrivialRelation (F := F) Vbase Rbase)
    (basis : Fin m → M) (v_idx r_idx : Fin m) (hne : v_idx ≠ r_idx)
    (hV : basis v_idx = Vbase) (hR : basis r_idx = Rbase) :
    AlgebraicRelationWitness (F := F) basis where
  coeffs := fun i => (if i = v_idx then rel.α else 0) + (if i = r_idx then rel.β else 0)
  nontrivial := by
    intro hzero
    have hα : rel.α = 0 := by
      have h := congrFun hzero v_idx
      simpa [hne] using h
    have hβ : rel.β = 0 := by
      have h := congrFun hzero r_idx
      simpa [Ne.symm hne] using h
    apply rel.nontrivial
    funext i
    rcases i with i | j
    · exact Fin.elim0 i
    · fin_cases j
      · exact hα
      · exact hβ
  relation := by
    have hsplit : representationEval basis
        (fun i => (if i = v_idx then rel.α else 0) + (if i = r_idx then rel.β else 0))
        = rel.α • basis v_idx + rel.β • basis r_idx := by
      simp only [representationEval, add_smul, ite_smul, zero_smul,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsplit, hV, hR]
    have hr := rel.relation
    simpa [NontrivialRelation.α, NontrivialRelation.β, representationEval,
      Fintype.sum_sum_type, Fin.sum_univ_two, augmentedBasis, BasisIndex.u,
      BasisIndex.w] using hr

/-- Compute the discrete log of `Vbase` base `Rbase` from a two-base relation, assuming `Rbase ≠ 0`. -/
def NontrivialRelation.toDiscreteLog [DecidableEq F] (Vbase Rbase : M)
    (r : NontrivialRelation (F := F) Vbase Rbase)
    (hR : Rbase ≠ 0) : DiscreteLogWitness (F := F) Rbase Vbase := by
  by_cases hα : r.α = 0
  · exfalso
    have hβ : r.β ≠ 0 := by
      intro hβ0
      apply r.nontrivial
      funext i
      rcases i with i | j
      · exact Fin.elim0 i
      · fin_cases j
        · exact hα
        · exact hβ0
    have hβR : r.β • Rbase = 0 := by
      calc r.β • Rbase
          = r.α • Vbase + r.β • Rbase := by
            rw [hα, zero_smul, zero_add]
        _ = 0 := by
            have hr := r.relation
            simpa [NontrivialRelation.α, NontrivialRelation.β, representationEval,
              Fintype.sum_sum_type, Fin.sum_univ_two, augmentedBasis, BasisIndex.u,
              BasisIndex.w] using hr
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
