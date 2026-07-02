import Zcash.Security.BindingSignature.Balance
import CompElliptic.Fields.Jubjub

/-!
# Sapling no-overflow bound (spec §4.13)

Sapling note values are *unsigned* 64-bit (`ValueType = {0..2^64−1}`), but the no-overflow argument
only needs `|v| ≤ 2^64 − 1` — the same per-element magnitude bound Orchard's signed net values
satisfy — so we bound `|vSum|` uniformly rather than reproducing the spec's tighter asymmetric range.
Any bound far below the Jubjub scalar field order suffices, and this one is.

The action counts are bounded *indirectly* by the 2 MB transaction-size limit (a transaction cannot
exceed the maximum block size of `2000000` bytes) against the minimum size of each description. We
reproduce those minimum sizes by summing the encoded field sizes (spec § Spend Description Encoding
and Consensus / § Output Description Encoding and Consensus) so a reviewer can check them, and — as
the spec does — we treat both v4 and v5 transactions: a v4 Spend carries a per-spend `anchor`
(32 bytes) that a v5 Spend omits (it is shared once per transaction), so the minimum Spend size is
384 bytes (v4) or 352 (v5).

Each byte/count magnitude is a named constant tied to the spec's quoted value by a single `example`.
This module discharges the `hbound` of `bundle_integer_balances_reduction` for Sapling, via `sapling_natAbs_lt`
and the byte-budget corollary `sapling_natAbs_lt_of_bytes`, both reducing to the shared
`natAbs_lt_of_vSumBound` in `Balance`.
-/

namespace Zcash.Security.BindingSignature

/-- The Jubjub scalar field order `ℓ` — the prime-order subgroup order, which is the scalar field of
the Sapling value commitment (spec § Jubjub). Imported from `CompElliptic.Fields.Jubjub`, where it
carries a Lucas/Pratt primality certificate. -/
@[reducible] def jubjubScalarOrder : ℕ := CompElliptic.Fields.Jubjub.JUBJUB_SCALAR_CARD

/-- Maximum transaction size in bytes: a transaction cannot exceed the maximum block size
(`2000000` bytes, a consensus rule). -/
def maxTxBytes : ℕ := 2000000

/-- Minimum bytes of a Sapling v4 Spend description (spec § Spend Description Encoding). -/
def saplingSpendBytesV4 : ℕ :=
  32 +    -- cv
  32 +    -- anchor (per-spend in v4)
  32 +    -- nullifier
  32 +    -- rk
  192 +   -- zkproof
  64      -- spendAuthSig

/-- Minimum bytes a Sapling Spend contributes to a v5 transaction. The `zkproof` (192) and
`spendAuthSig` (64) move to per-spend transaction-level vectors (`vSpendProofsSapling`,
`vSpendAuthSigs`) but are still counted once per spend; only the `anchor` (32) becomes shared
across the transaction. -/
def saplingSpendBytesV5 : ℕ :=
  32 +    -- cv
  32 +    -- nullifier
  32 +    -- rk
  192 +   -- zkproof      (in vSpendProofsSapling, per spend)
  64      -- spendAuthSig (in vSpendAuthSigs, per spend)

/-- It is sufficient to consider the minimum Sapling Spend contribution over v4 and v5. -/
def saplingMinSpendBytes : ℕ := min saplingSpendBytesV4 saplingSpendBytesV5

/-- Minimum bytes of a Sapling Output description (spec § Output Description Encoding); identical
for v4 and v5 (the v5 `zkproof` moves to `vOutputProofsSapling` but stays per-output). -/
def saplingOutputBytes : ℕ :=
  32 +    -- cv
  32 +    -- cmu
  32 +    -- ephemeralKey
  580 +   -- encCiphertext
  80 +    -- outCiphertext
  192     -- zkproof

example : saplingMinSpendBytes = 352 := by rfl
example : saplingOutputBytes = 948 := by rfl

/-- Maximum number of Spend descriptions. -/
def saplingMaxSpends : ℕ := maxTxBytes / saplingMinSpendBytes

/-- Maximum number of Output descriptions. -/
def saplingMaxOutputs : ℕ := maxTxBytes / saplingOutputBytes

example : saplingMaxSpends = 5681 := by rfl
example : saplingMaxOutputs = 2109 := by rfl

/-- Spend count from the byte budget: `n` spends of `≥ size` bytes fit in `≤ maxTxBytes` only if
`n ≤ maxTxBytes / size`. -/
theorem sapling_spend_count (n : ℕ) (h : saplingMinSpendBytes * n ≤ maxTxBytes) :
    n ≤ saplingMaxSpends := by
  simp only [saplingMaxSpends, maxTxBytes, show saplingMinSpendBytes = 352 from rfl] at h ⊢; omega

theorem sapling_output_count (m : ℕ) (h : saplingOutputBytes * m ≤ maxTxBytes) :
    m ≤ saplingMaxOutputs := by
  simp only [saplingOutputBytes, saplingMaxOutputs, maxTxBytes] at h ⊢; omega

/-- The Sapling `vSum` magnitude bound: each spend/output value has `|v| ≤ 2^64 − 1` and `vBalance`
has `|vBalance| ≤ 2^63`, over `≤ saplingMaxSpends` spends and `≤ saplingMaxOutputs` outputs, so
`|vSum| ≤ (saplingMaxSpends + saplingMaxOutputs)·(2^64 − 1) + 2^63`. Coarser than the spec's
asymmetric range, but any bound below the field order suffices for the no-overflow argument. -/
def saplingVSumBound : ℤ := vSumBound (saplingMaxSpends + saplingMaxOutputs)

/-- **Sapling no-overflow bound.** Spend/output values are range-proven to `0 ≤ v ≤ 2^64 − 1`
(hence `|v| ≤ 2^64 − 1`), over `≤ saplingMaxSpends` spends and `≤ saplingMaxOutputs` outputs, with
signed-64-bit `vBalance`. Concatenating the spends with the negated outputs (each still with
`|v| ≤ 2^64 − 1`) reduces to the shared `natAbs_lt_of_vSumBound`, exactly as Orchard does with its
net values. -/
theorem sapling_natAbs_lt {r : ℕ} (olds news : List ℤ) (vBalance : ℤ)
    (hOld : ∀ v ∈ olds, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hNew : ∀ v ∈ news, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hnOld : olds.length ≤ saplingMaxSpends)
    (hnNew : news.length ≤ saplingMaxOutputs)
    (hvBalance : |vBalance| ≤ 2^63)
    (hr : saplingVSumBound < (r : ℤ)) :
    (olds.sum - news.sum - vBalance).natAbs < r := by
  have hmapneg : (news.map Neg.neg).sum = -news.sum := by simp [List.sum_neg]
  have hv : ∀ v ∈ olds ++ news.map Neg.neg, |v| ≤ 2^64 - 1 := by
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact abs_le.mpr ⟨by linarith [(hOld v h).1, show (0:ℤ) ≤ 2^64 - 1 by norm_num], (hOld v h).2⟩
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
      exact abs_le.mpr
        ⟨by linarith [(hNew w hw).2], by linarith [(hNew w hw).1, show (0:ℤ) ≤ 2^64 - 1 by norm_num]⟩
  have hlen : (olds ++ news.map Neg.neg).length ≤ saplingMaxSpends + saplingMaxOutputs := by
    rw [List.length_append, List.length_map]; exact Nat.add_le_add hnOld hnNew
  have key := natAbs_lt_of_vSumBound (olds ++ news.map Neg.neg) vBalance
    (saplingMaxSpends + saplingMaxOutputs) hv hlen hvBalance hr
  rwa [List.sum_append, hmapneg, ← sub_eq_add_neg] at key

/-- Derive the spend/output counts from the 2 MB transaction-size limit (`n ≤ 5681`, `m ≤ 2109`),
then conclude via `sapling_natAbs_lt`. -/
theorem sapling_natAbs_lt_of_bytes {r : ℕ} (olds news : List ℤ) (vBalance : ℤ)
    (hOld : ∀ v ∈ olds, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hNew : ∀ v ∈ news, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hSpend : saplingMinSpendBytes * olds.length ≤ maxTxBytes)
    (hOutput : saplingOutputBytes * news.length ≤ maxTxBytes)
    (hvBalance : |vBalance| ≤ 2^63)
    (hr : saplingVSumBound < (r : ℤ)) :
    (olds.sum - news.sum - vBalance).natAbs < r :=
  sapling_natAbs_lt olds news vBalance hOld hNew
    (sapling_spend_count _ hSpend) (sapling_output_count _ hOutput) hvBalance hr

/-- The bound fits the Jubjub scalar field: the `hr` that instantiates `sapling_natAbs_lt` at
`r = jubjubScalarOrder` (and witnesses that the lemma is not vacuous). -/
theorem saplingVSumBound_lt_jubjubScalarOrder : saplingVSumBound < (jubjubScalarOrder : ℤ) := by
  simp only [saplingVSumBound, vSumBound,
             show saplingMaxSpends = 5681 from rfl,
             show saplingMaxOutputs = 2109 from rfl]
  norm_num [jubjubScalarOrder]

/-- **Sapling integer balance reduction (§4.13).** A verifying Sapling bundle — `≤ saplingMaxSpends`
spends and `≤ saplingMaxOutputs` outputs, each value in `[0, 2^64−1]`, signed-64-bit `vBalance` —
*either* balances over ℤ (`∑ v_old − ∑ v_new − vBalance = 0`) *or* exhibits a nontrivial
discrete-log relation between `V` and `R`. The no-overflow bound is discharged here by
`sapling_natAbs_lt`; there is no binding assumption (RedDSA extractability `hExtract` is the only
cryptographic input). The follow-on `sapling_bundle_balances_dlog` capstone collapses the relation
branch to the plain discrete log `dlog_R V` given `R ≠ 0`. -/
theorem sapling_bundle_balances_reduction {M : Type*} [AddCommGroup M]
    [Module (ZMod jubjubScalarOrder) M]
    (V R : M) (spends outputs : List (ℤ × ZMod jubjubScalarOrder)) (vBalance : ℤ)
    (bsk : ZMod jubjubScalarOrder)
    (hOld : ∀ v ∈ spends.map Prod.fst, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hNew : ∀ v ∈ outputs.map Prod.fst, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hnOld : spends.length ≤ saplingMaxSpends)
    (hnNew : outputs.length ≤ saplingMaxOutputs)
    (hvBalance : |vBalance| ≤ 2^63)
    (hExtract : bindingVK V R (castBundle spends) (castBundle outputs) (vBalance : ZMod jubjubScalarOrder)
      = bsk • R) :
    (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance = 0
      ∨ HasNontrivialRelation (F := ZMod jubjubScalarOrder) V R := by
  have hbound := sapling_natAbs_lt (spends.map Prod.fst) (outputs.map Prod.fst) vBalance
    hOld hNew (by simpa using hnOld) (by simpa using hnNew) hvBalance saplingVSumBound_lt_jubjubScalarOrder
  exact bundle_integer_balances_reduction V R spends outputs vBalance bsk hbound hExtract

/-- **Sapling balance / discrete-log capstone (§4.13).** A verifying Sapling bundle either balances
over ℤ or yields the plain discrete log of the value base `V` in the randomness base `R` (given
`R ≠ 0`) — the spec's reduction target. Caveat: `dlog_R V` always *exists* propositionally at the
deployed prime-order curve, so the disjunction is vacuous as a statement; the content is the explicit
reduction (`dlog_of_hasNontrivialRelation`), and the force — no feasible adversary *finds* the log —
is the computational DL layer outside Lean. -/
theorem sapling_bundle_balances_dlog {M : Type*} [AddCommGroup M]
    [Module (ZMod jubjubScalarOrder) M]
    (V R : M) (spends outputs : List (ℤ × ZMod jubjubScalarOrder)) (vBalance : ℤ)
    (bsk : ZMod jubjubScalarOrder)
    (hR : R ≠ 0)
    (hOld : ∀ v ∈ spends.map Prod.fst, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hNew : ∀ v ∈ outputs.map Prod.fst, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hnOld : spends.length ≤ saplingMaxSpends)
    (hnNew : outputs.length ≤ saplingMaxOutputs)
    (hvBalance : |vBalance| ≤ 2^63)
    (hExtract : bindingVK V R (castBundle spends) (castBundle outputs) (vBalance : ZMod jubjubScalarOrder)
      = bsk • R) :
    (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance = 0
      ∨ Nonempty (Zcash.Snark.DiscreteLogRepresentation (F := ZMod jubjubScalarOrder) R V) := by
  have hbound := sapling_natAbs_lt (spends.map Prod.fst) (outputs.map Prod.fst) vBalance
    hOld hNew (by simpa using hnOld) (by simpa using hnNew) hvBalance saplingVSumBound_lt_jubjubScalarOrder
  exact bundle_integer_balances_dlog V R spends outputs vBalance bsk hR hbound hExtract

end Zcash.Security.BindingSignature
