import Mathlib
import Zcash.Snark.Soundness.AGM

/-!
# Binding-signature balance: shared algebraic core

This module formalizes the algebraic heart of the Zcash binding-signature *balance* argument
(Zcash protocol specification §4.13 Sapling / §4.14 Orchard), abstracted over an arbitrary
`F`-module `M` so that it applies to both the Pallas (Orchard, Ironwood) and Jubjub (Sapling)
value-commitment groups. Here `F` will be instantiated with the scalar field `ZMod r`.

## The setting

Value commitments are `cv v rcv = v • V + rcv • R` for fixed generators `V` (value base) and
`R` (randomness base). For a bundle, the binding verification key is
`bvk = (∑ spend cv) − (∑ output cv) − v_balance • V`. Collecting the `V`- and `R`-terms (scalar
multiplication distributes over the value and randomness sums) this equals `A • V + B • R`, where
`A = ∑ v_in − ∑ v_out − v_balance` and `B = ∑ rcv_in − ∑ rcv_out`.

## How binding is expressed (and why not as "no relation exists")

In a prime-order group, `V` and `R` are *always* discrete-log-related — a nontrivial `(a,b)` with
`a • V + b • R = 0` exists; you simply cannot find it. So the information-theoretic statement
"the only relation is trivial" is *false* in the group setting and must not be used as the
binding hypothesis. Instead we phrase binding as a reduction:

* `§ Binding reduction` below proves, with no cryptographic hypothesis, that a non-balancing
  verifying bundle *exhibits* an explicit nontrivial relation between `V` and `R`
  (`relation_of_imbalance`), or equivalently the discrete log `dlog_R V`
  (`imbalance_yields_discrete_log`).

  "The bundle balances" then reduces to the discrete-log relation problem (DLR); for the two-slot
  binding pair this collapses further to the plain discrete log `dlog_R V` given `R ≠ 0`
  (`dlog_of_hasNontrivialRelation`, consumed by the `*_dlog` capstones). This is the
  shape of the spec's argument: *if you can unbalance, you can solve DL*. The relation and
  discrete-log problems are tightly equivalent (Jaeger and Tessaro, https://eprint.iacr.org/2020/1213
  Lemma 3 in general, but this case is very simple), so this is no stronger than DL.

The range / no-overflow lift from field balance to integer balance is already built (`§ Integer
balance` below: `intBalance_eq_zero_of_lt`, discharged per pool by `orchard_natAbs_lt` /
`sapling_natAbs_lt` from the 64-bit value-type ranges).

## Assumptions

* **RedDSA extractability** (`bvk = bsk • R` from a verifying binding signature) — assumed, not
  proved (its proof needs a random oracle + forking); supplied as the `hExtract` hypothesis.
* **DLR hardness** — the assumption the reduction discharges against to conclude actual balance
  (the discrete-log relation problem, tightly equivalent to DL).

## DLR-to-DL handoff

For the two-slot binding pair, the generic fixed-slot AGM game (`Zcash.Snark.Soundness.AGM`)
degenerates: placing the DL challenge at the `V` slot over `base := R` leaves `R` itself as the only
non-challenge slot (known log `1`), so no auxiliary base or known-log embedding is needed, and the
relation branch collapses directly to `dlog_R V` given `R ≠ 0` (`dlog_of_hasNontrivialRelation`,
matching `imbalance_yields_discrete_log`). `relationWitnessOfBindingRelation` additionally records
the binding relation as a generic `Zcash.Snark.AlgebraicRelationWitness` over the `(V, R)` basis for
consumers of the generic layer.

## Not yet built

* The probabilistic / oracle-machine wrapper (adversary success accounting) and the algebraic-prover
  model in which relation witnesses come from prover-output representations rather than from the
  existential relation branch — see the module docs of `Zcash.Snark.Soundness.AGM` and issue #15.
-/

namespace Zcash.Security.BindingSignature

variable {F : Type*} [Field F]
variable {M : Type*} [AddCommGroup M] [Module F M]

/-- From RedDSA extractability (`bvk = bsk • R`) and the decomposition of the binding
verification key (`bvk = A • V + B • R`), the value coefficient satisfies `A • V = (bsk − B) • R`.
True unconditionally (pure module algebra). -/
theorem smul_value_eq_smul_rand (V R bvk : M) (A B bsk : F)
    (hExtract : bvk = bsk • R) (hSum : bvk = A • V + B • R) :
    A • V = (bsk - B) • R := by
  have h : A • V + B • R = bsk • R := by rw [← hSum, hExtract]
  calc A • V = bsk • R - B • R := eq_sub_of_add_eq h
    _ = (bsk - B) • R := (sub_smul bsk B R).symm

/-! ### Binding reduction -/

/-- A non-balancing (`A ≠ 0`) verifying bundle exhibits an explicit nontrivial discrete-log
relation between the value base `V` and the randomness base `R`: the coefficients `(A, B − bsk)`
are not both zero (indeed `A ≠ 0`) and `A • V + (B − bsk) • R = 0`.

Such a relation always exists in the group; the content is that imbalance *produces* one.
Under hardness of the discrete-log relation problem, that cannot happen, so the bundle balances. -/
theorem relation_of_imbalance (V R bvk : M) (A B bsk : F)
    (hA : A ≠ 0)
    (hExtract : bvk = bsk • R) (hSum : bvk = A • V + B • R) :
    A ≠ 0 ∧ A • V + (B - bsk) • R = 0 := by
  refine ⟨hA, ?_⟩
  rw [smul_value_eq_smul_rand V R bvk A B bsk hExtract hSum, ← add_smul]
  have hc : (bsk - B) + (B - bsk) = (0 : F) := by ring
  rw [hc, zero_smul]

/-- A non-balancing verifying bundle yields the discrete log of `V` base `R`, namely
`dlog_R V = A⁻¹ (bsk − B)`. This is just a more explicit way of saying `relation_of_imbalance`;
it is the latter that is wired into the balance reduction below. -/
theorem imbalance_yields_discrete_log (V R bvk : M) (A B bsk : F) (hA : A ≠ 0)
    (hExtract : bvk = bsk • R) (hSum : bvk = A • V + B • R) :
    V = (A⁻¹ * (bsk - B)) • R := by
  have hVR := smul_value_eq_smul_rand V R bvk A B bsk hExtract hSum
  have h : A⁻¹ • (A • V) = A⁻¹ • ((bsk - B) • R) := by rw [hVR]
  rwa [smul_smul, smul_smul, inv_mul_cancel₀ hA, one_smul] at h

/-- A nontrivial `F`-linear (discrete-log) relation between the value base `V` and the randomness
base `R`: scalars `(a, b)` not both zero with `a • V + b • R = 0`. The content of the binding
reduction is that imbalance allows constructing such a relation explicitly. -/
def HasNontrivialRelation (V R : M) : Prop := ∃ a b : F, (a ≠ 0 ∨ b ≠ 0) ∧ a • V + b • R = 0

/-! ### AGM handoff for the binding relation -/

/-- The two public bases used by the binding-signature relation: value base `V`, randomness base `R`. -/
def bindingSignatureBasis (V R : M) : Fin 2 → M
  | 0 => V
  | 1 => R

/-- The two coefficients of a binding-signature relation over `(V, R)`. -/
def bindingSignatureCoeffs (a b : F) : Fin 2 → F
  | 0 => a
  | 1 => b

/-- The generic AGM representation evaluator specializes to the binding-signature two-base MSM. -/
theorem representationEval_bindingSignatureBasis (V R : M) (a b : F) :
    Zcash.Snark.representationEval (bindingSignatureBasis V R) (bindingSignatureCoeffs a b)
      = a • V + b • R := by
  simp [Zcash.Snark.representationEval, bindingSignatureBasis, bindingSignatureCoeffs,
    Fin.sum_univ_two]

/-- A concrete binding-signature relation is the same AGM relation witness over the public basis `(V,R)`. -/
def relationWitnessOfBindingRelation (V R : M) (a b : F)
    (hnt : a ≠ 0 ∨ b ≠ 0) (hrel : a • V + b • R = 0) :
    Zcash.Snark.AlgebraicRelationWitness (F := F) (bindingSignatureBasis V R) :=
  { coeffs := bindingSignatureCoeffs a b
    nontrivial := by
      intro hzero
      have ha : a = 0 := by
        have h := congrFun hzero 0
        simpa [bindingSignatureCoeffs] using h
      have hb : b = 0 := by
        have h := congrFun hzero 1
        simpa [bindingSignatureCoeffs] using h
      rcases hnt with ha_ne | hb_ne
      · exact ha_ne ha
      · exact hb_ne hb
    relation := by
      rw [representationEval_bindingSignatureBasis, hrel] }

/-- **Two-slot collapse to `dlog_R V`.** From a nontrivial relation `a • V + b • R = 0` with
`R ≠ 0`, the discrete log of `V` base `R`: if `a ≠ 0` the relation solves for `V`; if `a = 0` then
`b ≠ 0` forces `R = 0`, a contradiction. This is the fixed-slot AGM game
(`Zcash.Snark.FixedSlotEmbedding`) degenerated to the binding pair: with `base := R` and the DL
challenge pre-placed at the `V` slot, the only non-challenge slot is `R` itself (known log `1`), so
no auxiliary base or embedding hypothesis is needed, and the miss event `a = 0` is void for `R ≠ 0` —
matching the spec's reduction target and `imbalance_yields_discrete_log`.

Caveat (as for the relation form this consumes): `dlog_R V` always *exists* propositionally in a
cyclic prime-order group, so a `∨ Nonempty (DiscreteLogRepresentation R V)` conclusion is vacuous as
a statement; the content is the explicit construction, and the force — no feasible adversary can
*find* the log — is the computational DL layer outside Lean. -/
theorem dlog_of_hasNontrivialRelation (V R : M) (hR : R ≠ 0)
    (hrel : HasNontrivialRelation (F := F) V R) :
    Nonempty (Zcash.Snark.DiscreteLogRepresentation (F := F) R V) := by
  obtain ⟨a, b, hnt, hab⟩ := hrel
  by_cases ha : a = 0
  · exfalso
    have hb : b ≠ 0 := by
      rcases hnt with h0 | hb
      · exact absurd ha h0
      · exact hb
    have hbR : b • R = 0 := by
      simpa [ha] using hab
    have hR0 : R = 0 := by
      have h := congrArg (fun X : M => b⁻¹ • X) hbR
      simpa [smul_smul, inv_mul_cancel₀ hb] using h
    exact hR hR0
  · refine ⟨⟨-(a⁻¹ * b), ?_⟩⟩
    have hV : a • V = -(b • R) := eq_neg_of_add_eq_zero_left hab
    have h2 : V = a⁻¹ • -(b • R) := by
      have h := congrArg (fun X : M => a⁻¹ • X) hV
      simpa [smul_smul, inv_mul_cancel₀ ha] using h
    rw [h2, smul_neg, smul_smul, neg_smul]

/-- **Balance reduction (field level).** From RedDSA extractability (`bvk = bsk • R`) and the
binding-key decomposition (`bvk = A • V + B • R`), with no other cryptographic hypothesis:
*either* the net value coefficient is zero (`A = 0`, balance modulo the scalar-field order),
*or* the bundle exhibits a nontrivial discrete-log relation between `V` and `R`. -/
theorem value_coeff_zero_reduction (V R bvk : M) (A B bsk : F)
    (hExtract : bvk = bsk • R) (hSum : bvk = A • V + B • R) :
    A = 0 ∨ HasNontrivialRelation (F := F) V R := by
  by_cases hA : A = 0
  · exact Or.inl hA
  · obtain ⟨hA', hrel⟩ := relation_of_imbalance V R bvk A B bsk hA hExtract hSum
    exact Or.inr ⟨A, B - bsk, Or.inl hA', hrel⟩

/-! ### Integer balance: range / no-overflow lift

The binding reduction `value_coeff_zero_reduction` concludes `A = 0` in `F = ZMod r`
(or exhibits a discrete-log relation), i.e. balance *modulo the scalar-field order*.
Genuine balance is the integer equation `∑ v_in − ∑ v_out − v_balance = 0`.

That balance modulo the scalar-field order implies integer balance is argued in the second
half of each of §4.13 and §4.14: "... we will also demonstrate that it does not overflow
`ValueCommitType`"). The net value `vSum` cannot wrap mod `r`, because each note value is
range-proven and the spend/output/action count is bounded, so `vSum ∈ ValueCommitType ⊂ (−r, r)`
and `vSum = 0 (mod r)` forces `vSum = 0` over ℤ.

This argument deliberately uses the *value-type* range —not `[-MAX_MONEY, MAX_MONEY]`—
so that it works for any signed-64-bit `valueBalance`, which is all the encoding constrains.

The per-pool bounds live in the `Orchard` and `Sapling` modules: `orchard_natAbs_lt` /
`sapling_natAbs_lt` (with `_v4` / `_v5` corollaries) derive `N.natAbs < r` from the value-type
range proofs and the field order, producing the `hbound` consumed by
`bundle_integer_balances_reduction`.
The per-pool reasoning is documented there — Orchard's signed net values under the consensus
rule `n ≤ 2^16 − 1`, and Sapling's unsigned values under the transaction-size limit. -/

/-- No-overflow: an integer reducing to `0` mod `r` whose magnitude is `< r` is `0`.
This turns balance modulo the scalar-field order (`A = 0` in `ZMod r`) into integer balance,
given that the value sums cannot wrap. -/
theorem intBalance_eq_zero_of_lt {r : ℕ} [NeZero r] (N : ℤ)
    (hmod : (N : ZMod r) = 0) (hlt : N.natAbs < r) : N = 0 := by
  obtain ⟨k, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd N r).mp hmod
  rcases eq_or_ne k 0 with hk | hk
  · simp [hk]
  · have hpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
    have habs : ((r : ℤ) * k).natAbs = r * k.natAbs := by simp [Int.natAbs_mul]
    rw [habs] at hlt
    have hle : r ≤ r * k.natAbs := by
      calc r = r * 1 := (Nat.mul_one r).symm
        _ ≤ r * k.natAbs := Nat.mul_le_mul (le_refl r) hpos
    omega

/-- The same conclusion phrased with an integer absolute-value bound `|N| < r`. -/
theorem intBalance_eq_zero_of_abs_lt {r : ℕ} [NeZero r] (N : ℤ)
    (hmod : (N : ZMod r) = 0) (hlt : |N| < (r : ℤ)) : N = 0 := by
  apply intBalance_eq_zero_of_lt N hmod
  rwa [Int.abs_eq_natAbs, Nat.cast_lt] at hlt

/-! ### Deriving the decomposition from a bundle (linearity of the value commitment)

The hypothesis `bvk = A • V + B • R` consumed above is not an assumption: it can be derived
from the value commitment `cv v rcv = v • V + rcv • R` being `F`-linear in `(v, rcv)`,
and the shape of a bundle — lists of spend / output `(value, randomness)` pairs together
with the declared `vBalance`. -/

/-- The value commitment `cv v rcv = v • V + rcv • R`. -/
def valueCommit (V R : M) (v rcv : F) : M := v • V + rcv • R

/-- A sum of value commitments decomposes as the value-sum times `V` plus the randomness-sum
times `R`. `•` distributes over the value and randomness sums. -/
theorem sum_valueCommit (V R : M) (l : List (F × F)) :
    (l.map fun p => valueCommit V R p.1 p.2).sum
      = (l.map Prod.fst).sum • V + (l.map Prod.snd).sum • R := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simp only [valueCommit, add_smul]
    abel

/-- The binding verification key of a bundle: `bvk = (∑ spend cv) − (∑ output cv) − v_balance • V`. -/
def bindingVK (V R : M) (spends outputs : List (F × F)) (vBalance : F) : M :=
  (spends.map fun p => valueCommit V R p.1 p.2).sum
    - (outputs.map fun p => valueCommit V R p.1 p.2).sum - vBalance • V

/-- **`hSum`, derived.** The binding verification key decomposes linearly as `A • V + B • R`,
with `A` the net value (`∑ spend values − ∑ output values − vBalance`) and `B` the net randomness
(`∑ spend randomness − ∑ output randomness`). -/
theorem bindingVK_decomp (V R : M) (spends outputs : List (F × F)) (vBalance : F) :
    bindingVK V R spends outputs vBalance
      = ((spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance) • V
        + ((spends.map Prod.snd).sum - (outputs.map Prod.snd).sum) • R := by
  rw [bindingVK, sum_valueCommit, sum_valueCommit]
  simp only [sub_smul]
  abel

/-- **Bundle balance reduction (field level).** For a bundle whose binding signature verifies
(`hExtract`, from RedDSA extractability): *either* the net value balances modulo the scalar-field
order, *or* the bundle exhibits a nontrivial discrete-log relation between `V` and `R`. There is no
binding assumption; the decomposition `hSum` is derived by `bindingVK_decomp`. This is not yet
integer balance — lifting `A = 0` to `∑ v_in = ∑ v_out + v_balance` over ℤ needs the no-overflow
step `intBalance_eq_zero_of_lt` (applied in `bundle_integer_balances_reduction`); discharging the
relation branch needs DLR hardness at the computational layer. -/
theorem bundle_mod_balances_reduction (V R : M) (spends outputs : List (F × F)) (vBalance bsk : F)
    (hExtract : bindingVK V R spends outputs vBalance = bsk • R) :
    (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance = 0
      ∨ HasNontrivialRelation (F := F) V R :=
  value_coeff_zero_reduction V R (bindingVK V R spends outputs vBalance) _ _ bsk hExtract
    (bindingVK_decomp V R spends outputs vBalance)

/-- Cast an integer-valued bundle (integer note / net values, field randomness) to a field-valued one,
sending each value `v : ℤ` to its image `(v : ZMod r)` in the value commitment. -/
def castBundle {r : ℕ} (l : List (ℤ × ZMod r)) : List (ZMod r × ZMod r) :=
  l.map fun p => ((p.1 : ZMod r), p.2)

/-- The value-sum of a cast bundle is the `ZMod r` image of the integer value-sum, because `Int.cast`
is additive. This is what lets the integer↔field cast be *derived* rather than assumed. -/
theorem castBundle_fst_sum {r : ℕ} (l : List (ℤ × ZMod r)) :
    ((castBundle l).map Prod.fst).sum = (((l.map Prod.fst).sum : ℤ) : ZMod r) := by
  induction l with
  | nil => simp [castBundle]
  | cons a t ih =>
    simp only [castBundle, List.map_cons, List.sum_cons, Int.cast_add] at ih ⊢
    rw [ih]

/-- **Integer balance reduction** — the second half of the spec §4.13 / §4.14 argument, over a bundle
whose values are the actual integer note / net values (`ℤ`), with field randomness. Given the no-overflow
bound `hbound`, this lifts the field-level reduction to ℤ: *either* the bundle balances over ℤ
(`∑ v_in − ∑ v_out − vBalance = 0`) *or* it exhibits a nontrivial discrete-log relation between `V`
and `R`. There is no binding assumption — the relation branch is discharged against DLR hardness at
the computational layer.

The integer→field cast is derived using `castBundle_fst_sum`; the only added input over the field
reduction is the no-overflow bound `hbound`, provided by protocol-specific value-type range proofs
(`BindingSignature.Orchard.orchard_natAbs_lt` and `BindingSignature.Sapling.sapling_natAbs_lt`). -/
theorem bundle_integer_balances_reduction {r : ℕ} [Fact (Nat.Prime r)]
    {M : Type*} [AddCommGroup M] [Module (ZMod r) M]
    (V R : M) (spends outputs : List (ℤ × ZMod r)) (vBalance : ℤ) (bsk : ZMod r)
    (hbound : ((spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance).natAbs < r)
    (hExtract : bindingVK V R (castBundle spends) (castBundle outputs) (vBalance : ZMod r) = bsk • R) :
    (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance = 0
      ∨ HasNontrivialRelation (F := ZMod r) V R := by
  haveI : NeZero r := ⟨(Fact.out : Nat.Prime r).pos.ne'⟩
  rcases bundle_mod_balances_reduction V R (castBundle spends) (castBundle outputs)
      (vBalance : ZMod r) bsk hExtract with hmod | hrel
  · refine Or.inl (intBalance_eq_zero_of_lt _ ?_ hbound)
    rw [castBundle_fst_sum, castBundle_fst_sum] at hmod
    rw [Int.cast_sub, Int.cast_sub]
    exact hmod
  · exact Or.inr hrel

/-! ### Generic integer-range helpers for the no-overflow lift

These discharge the `hbound`/`hlt` hypothesis of the lifts above from value-type range bounds. The
Orchard- and Sapling-specific instances — the concrete byte / action-count bounds, the `vSum` range
constants, and the field orders — live in `Zcash.Security.BindingSignature.Orchard` and `.Sapling`. -/

/-- Triangle bound for a list sum: if every element has `|x| ≤ M`, the sum has `|∑| ≤ length · M`. -/
theorem abs_listSum_le {l : List ℤ} {M : ℤ} (h : ∀ x ∈ l, |x| ≤ M) :
    |l.sum| ≤ (l.length : ℤ) * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : |a| ≤ M := h a List.mem_cons_self
    have ht : |t.sum| ≤ (t.length : ℤ) * M := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    calc |(a :: t).sum| = |a + t.sum| := by rw [List.sum_cons]
      _ ≤ |a| + |t.sum| := abs_add_le a t.sum
      _ ≤ M + (t.length : ℤ) * M := add_le_add ha ht
      _ = ((a :: t).length : ℤ) * M := by rw [List.length_cons]; push_cast; ring

/-- From a magnitude bound `|N| ≤ B` and the field-order gap `B < r`, the residue `N.natAbs < r`. -/
theorem natAbs_lt_of_abs_le {r : ℕ} {N B : ℤ} (hN : |N| ≤ B) (hr : B < (r : ℤ)) :
    N.natAbs < r := by
  have h : (N.natAbs : ℤ) < (r : ℤ) := by rw [← Int.abs_eq_natAbs]; exact lt_of_le_of_lt hN hr
  exact_mod_cast h

/-- The `vSum` magnitude bound for at most `N` values each with `|v| ≤ 2^64 − 1` and a signed-64-bit
balance: `N · (2^64 − 1) + 2^63`. Each pool's bound is an instance (see `Orchard` / `Sapling`). -/
def vSumBound (N : ℕ) : ℤ := (N : ℤ) * (2^64 - 1) + 2^63

/-- Shared no-overflow bound. `N` values each range-proven to `|v| ≤ 2^64 − 1`, with a signed-64-bit
`vBalance` (`|vBalance| ≤ 2^63`), give `(vs.sum − vBalance).natAbs < r` once `vSumBound N < r`. This
is the common core of both pools' bounds: Orchard applies it to its net values directly; Sapling to
the spend values concatenated with the negated output values (each still has `|v| ≤ 2^64 − 1`). -/
theorem natAbs_lt_of_vSumBound {r : ℕ} (vs : List ℤ) (vBalance : ℤ) (N : ℕ)
    (hv : ∀ v ∈ vs, |v| ≤ 2^64 - 1)
    (hn : vs.length ≤ N)
    (hvb : |vBalance| ≤ 2^63)
    (hr : vSumBound N < (r : ℤ)) :
    (vs.sum - vBalance).natAbs < r := by
  refine natAbs_lt_of_abs_le ?_ hr
  simp only [vSumBound]
  have hlen : (vs.length : ℤ) ≤ (N : ℤ) := by exact_mod_cast hn
  have hs : |vs.sum| ≤ (N : ℤ) * (2^64 - 1) :=
    le_trans (abs_listSum_le hv) (mul_le_mul_of_nonneg_right hlen (by norm_num))
  calc |vs.sum - vBalance| ≤ |vs.sum| + |vBalance| := abs_sub _ _
    _ ≤ (N : ℤ) * (2^64 - 1) + 2^63 := add_le_add hs hvb

end Zcash.Security.BindingSignature
