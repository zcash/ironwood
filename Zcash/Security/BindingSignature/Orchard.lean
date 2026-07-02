import Zcash.Security.BindingSignature.Balance
import CompElliptic.Fields.Pasta

/-!
# Orchard no-overflow bound (spec §4.14)

The Orchard action count is bounded *directly* by a dedicated consensus rule `n ≤ 2^16 − 1`,
independent of the transaction size (the spec notes this is technically redundant given the
2 MB limit, but it stands on its own). Each action commits to the signed *net* value
`v = v_spend − v_output`, range-proven by the Action statement to lie in
`SignedValueDifferenceType = [−2^64+1, 2^64−1]`, i.e. `|v| ≤ 2^64 − 1`.

This module instantiates the generic `natAbs_lt_of_abs_le` from `Balance` at those concrete bounds,
discharging the `hbound` hypothesis of `bundle_integer_balances_reduction` for Orchard.
-/

namespace Zcash.Security.BindingSignature

/-- The Pallas scalar field order `r_ℙ` — the order of the Pallas group, which is the scalar field of
the Orchard value commitment (spec § Pallas and Vesta). Imported from `CompElliptic.Fields.Pasta`,
where it carries a Lucas/Pratt primality certificate. -/
@[reducible] def pallasScalarOrder : ℕ := CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD

/-- The Orchard `vSum` magnitude bound = the spec's `ValueCommitTypeOrchard` subrange endpoint
`(2^16 − 1)·(2^64 − 1) + 2^63`, from `|v| ≤ 2^64 − 1` per action, the consensus rule `n ≤ 2^16 − 1`,
and the signed-64-bit `vBalance`. -/
def orchardVSumBound : ℤ := vSumBound (2^16 - 1)

/-- The bound equals the spec's quoted endpoint. -/
example : orchardVSumBound = 1208916596242592319864833 := by norm_num [orchardVSumBound, vSumBound]

/-- **Orchard no-overflow bound.** With `|v| ≤ 2^64 − 1` per action, `n ≤ 2^16 − 1` actions, and
`|vBalance| ≤ 2^63`, the net sum `vSum = ∑ v − vBalance` has `vSum.natAbs < r` once
`orchardVSumBound < r` — directly from the shared `natAbs_lt_of_vSumBound`. This is the `hbound` of
`bundle_integer_balances_reduction` for Orchard. -/
theorem orchard_natAbs_lt {r : ℕ} (vs : List ℤ) (vBalance : ℤ)
    (hv : ∀ v ∈ vs, |v| ≤ 2^64 - 1)
    (hn : vs.length ≤ 2^16 - 1)
    (hvBalance : |vBalance| ≤ 2^63)
    (hr : orchardVSumBound < (r : ℤ)) :
    (vs.sum - vBalance).natAbs < r :=
  natAbs_lt_of_vSumBound vs vBalance (2^16 - 1) hv hn hvBalance hr

/-- The bound fits the Pallas scalar field: the `hr` that instantiates `orchard_natAbs_lt` at
`r = pallasScalarOrder` (and witnesses that the lemma is not vacuous). -/
theorem orchardVSumBound_lt_pallasScalarOrder : orchardVSumBound < (pallasScalarOrder : ℤ) := by
  norm_num [orchardVSumBound, vSumBound, pallasScalarOrder]

/-- **Orchard integer balance reduction (§4.14).** A verifying Orchard bundle of `≤ 2^16 − 1`
actions — each committing a net value `v ∈ [−2^64+1, 2^64−1]`, with signed-64-bit `vBalance` —
*either* balances over ℤ (`∑ v_net − vBalance = 0`) *or* exhibits a nontrivial discrete-log relation
between `V` and `R`. The no-overflow bound is discharged here by `orchard_natAbs_lt`; there is no
binding assumption (RedDSA extractability `hExtract` is the only cryptographic input). The follow-on
`orchard_bundle_balances_dlog` capstone collapses the relation branch to the plain discrete log
`dlog_R V` given `R ≠ 0`. -/
theorem orchard_bundle_balances_reduction {M : Type*} [AddCommGroup M]
    [Module (ZMod pallasScalarOrder) M]
    (V R : M) (actions : List (ℤ × ZMod pallasScalarOrder)) (vBalance : ℤ)
    (bsk : ZMod pallasScalarOrder)
    (hv : ∀ v ∈ actions.map Prod.fst, |v| ≤ 2^64 - 1)
    (hn : actions.length ≤ 2^16 - 1)
    (hvBalance : |vBalance| ≤ 2^63)
    (hExtract : bindingVK V R (castBundle actions) (castBundle []) (vBalance : ZMod pallasScalarOrder)
      = bsk • R) :
    (actions.map Prod.fst).sum - vBalance = 0
      ∨ HasNontrivialRelation (F := ZMod pallasScalarOrder) V R := by
  have hbound := orchard_natAbs_lt (actions.map Prod.fst) vBalance hv (by simpa using hn) hvBalance
    orchardVSumBound_lt_pallasScalarOrder
  simpa using
    bundle_integer_balances_reduction V R actions [] vBalance bsk (by simpa using hbound) hExtract

/-- **Orchard balance / discrete-log capstone (§4.14).** A verifying Orchard bundle either balances
over ℤ or yields the plain discrete log of the value base `V` in the randomness base `R` (given
`R ≠ 0`) — the spec's reduction target. Caveat: `dlog_R V` always *exists* propositionally at the
deployed prime-order curve, so the disjunction is vacuous as a statement; the content is the explicit
reduction (`dlog_of_hasNontrivialRelation`), and the force — no feasible adversary *finds* the log —
is the computational DL layer outside Lean. -/
theorem orchard_bundle_balances_dlog {M : Type*} [AddCommGroup M]
    [Module (ZMod pallasScalarOrder) M]
    (V R : M) (actions : List (ℤ × ZMod pallasScalarOrder)) (vBalance : ℤ)
    (bsk : ZMod pallasScalarOrder)
    (hR : R ≠ 0)
    (hv : ∀ v ∈ actions.map Prod.fst, |v| ≤ 2^64 - 1)
    (hn : actions.length ≤ 2^16 - 1)
    (hvBalance : |vBalance| ≤ 2^63)
    (hExtract : bindingVK V R (castBundle actions) (castBundle []) (vBalance : ZMod pallasScalarOrder)
      = bsk • R) :
    (actions.map Prod.fst).sum - vBalance = 0
      ∨ Nonempty (Zcash.Snark.DiscreteLogRepresentation (F := ZMod pallasScalarOrder) R V) := by
  have hbound := orchard_natAbs_lt (actions.map Prod.fst) vBalance hv (by simpa using hn) hvBalance
    orchardVSumBound_lt_pallasScalarOrder
  simpa using
    bundle_integer_balances_dlog V R actions [] vBalance bsk hR (by simpa using hbound) hExtract

end Zcash.Security.BindingSignature
