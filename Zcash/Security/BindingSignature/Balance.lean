import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Common.DiscreteLogRelation

/-!
# Binding-signature balance: shared algebraic core

This module formalizes the algebraic heart of the Zcash binding-signature *balance* argument
(Zcash protocol specification §4.13 Sapling / §4.14 Orchard), abstracted over an arbitrary
`F`-module `M` so that it applies to both the Pallas (Orchard, Ironwood) and Jubjub (Sapling)
value-commitment groups. Here `F` will be instantiated with the scalar field `ZMod r`.

## The setting

Value commitments are `cv v rcv = v • Vbase + rcv • Rbase` for fixed generators `Vbase` (value base) and
`Rbase` (randomness base). For a bundle, the binding verification key is
`bvk = (∑ spend cv) − (∑ output cv) − v_balance • Vbase`. Collecting the `Vbase`- and `Rbase`-terms (scalar
multiplication distributes over the value and randomness sums) this equals `A • Vbase + B • Rbase`, where
`A = ∑ v_in − ∑ v_out − v_balance` and `B = ∑ rcv_in − ∑ rcv_out`.

## How binding is expressed (and why not as "no relation exists")

In a prime-order group, `Vbase` and `Rbase` are *always* discrete-log-related — a nontrivial `(a,b)` with
`a • Vbase + b • Rbase = 0` exists; you simply cannot find it. So the information-theoretic statement
"the only relation is trivial" is *false* in the group setting and must not be used as the
binding hypothesis. Instead we phrase binding as a reduction:

* `§ Binding reduction` below shows, with no cryptographic hypothesis, that a non-balancing
  verifying bundle *exhibits* an explicit nontrivial relation between `Vbase` and `Rbase`, or
  equivalently the discrete log `dlog_Rbase Vbase` (`imbalance_yields_discrete_log`).
  `NontrivialRelation.ofImbalance` outputs the break as computed data
  <https://zcash.github.io/ironwood/formal-verification.html#breaks-as-computed-data>; an
  ∃-closed relation Prop would be vacuous, since a relation always exists in a prime-order
  group.

  `Zcash.Security.BindingSignature.DiscreteLog` turns the computed Orchard and Sapling relations
  into plain-DL solutions: *if you can unbalance, you can solve DL*. DLR and DL are tightly equivalent
  (Jaeger and Tessaro, https://eprint.iacr.org/2020/1213, Lemma 3), so this assumes no more than DL
  hardness.

The range / no-overflow lift from field balance to integer balance is already built (`§ Integer
balance` below: `intBalance_eq_zero_of_lt`, discharged per pool by `orchard_natAbs_lt` /
`sapling_natAbs_lt` from the 64-bit value-type ranges). What remains is cryptographic and
computational, not algebraic:

## Assumptions

* **RedDSA extractability** (`bvk = bsk • Rbase` from a verifying binding signature) — assumed, not
  proved (its proof needs a random oracle + forking); supplied as the `hExtract` hypothesis.
* **Discrete-log hardness** — consumed by the AGM layer after the computed relation-to-DL handoff;
  alternatively one may assume DLR hardness directly at this lower layer.
-/

namespace Zcash.Security.BindingSignature

variable {F : Type*} [Field F]
variable {M : Type*} [AddCommGroup M] [Module F M]

/-- From RedDSA extractability (`bvk = bsk • Rbase`) and the decomposition of the binding
verification key (`bvk = A • Vbase + B • Rbase`), the value coefficient satisfies `A • Vbase = (bsk − B) • Rbase`.
True unconditionally (pure module algebra). -/
theorem smul_value_eq_smul_rand (Vbase Rbase bvk : M) (A B bsk : F)
    (hExtract : bvk = bsk • Rbase) (hSum : bvk = A • Vbase + B • Rbase) :
    A • Vbase = (bsk - B) • Rbase := by
  have h : A • Vbase + B • Rbase = bsk • Rbase := by rw [← hSum, hExtract]
  calc A • Vbase = bsk • Rbase - B • Rbase := eq_sub_of_add_eq h
    _ = (bsk - B) • Rbase := (sub_smul bsk B Rbase).symm

/-! ### Binding reduction -/

/-- A non-balancing verifying bundle yields the discrete log of `Vbase` base `Rbase`, namely
`dlog_Rbase Vbase = A⁻¹ (bsk − B)`. This is a more explicit way of reading the relation computed by
`NontrivialRelation.ofImbalance`; it is the latter that is wired into the balance reduction
below. -/
theorem imbalance_yields_discrete_log (Vbase Rbase bvk : M) (A B bsk : F) (hA : A ≠ 0)
    (hExtract : bvk = bsk • Rbase) (hSum : bvk = A • Vbase + B • Rbase) :
    Vbase = (A⁻¹ * (bsk - B)) • Rbase := by
  have hVR := smul_value_eq_smul_rand Vbase Rbase bvk A B bsk hExtract hSum
  have h : A⁻¹ • (A • Vbase) = A⁻¹ • ((bsk - B) • Rbase) := by rw [hVR]
  rwa [smul_smul, smul_smul, inv_mul_cancel₀ hA, one_smul] at h

/-- A nontrivial `F`-linear (discrete-log) relation between the value base `Vbase` and the
randomness base `Rbase`, as data: scalars not both zero with `· • Vbase + · • Rbase = 0`.
It is the shared `Zcash.NontrivialRelation` at the two bases (its generator vector
`g` empty, `U`/`W` the bases `Vbase`, `Rbase`), so the two coefficients are its
`α`/`β`. Such a
relation always *exists* propositionally in a prime-order group, so an ∃-closed Prop
version would be vacuous; the content of the binding reduction is that imbalance lets us
*compute* one (breaks as computed data — see `Zcash.Security.RandomOracle`). -/
abbrev NontrivialRelation (Vbase Rbase : M) : Type _ :=
  Zcash.NontrivialRelation (F := F) (Fin.elim0 : Fin 0 → M) Vbase Rbase

/-- **Balance reduction (field level), as a computed relation.** From RedDSA extractability
(`bvk = bsk • Rbase`), the binding-key decomposition (`bvk = A • Vbase + B • Rbase`), and imbalance
(`A ≠ 0`), compute the explicit nontrivial relation with coefficients `(A, B − bsk)`. Such a
relation always exists in the group; the content is that imbalance *produces* one.

This is the algebraic core; the consumer-facing forms are the bundle-level reductions below
(`ofBundleModImbalance`, `ofBundleIntImbalance`, and the per-pool capstones), which derive
the decomposition and supply the imbalance hypothesis at the bundle values. -/
def NontrivialRelation.ofImbalance (Vbase Rbase bvk : M) (A B bsk : F) (hA : A ≠ 0)
    (hExtract : bvk = bsk • Rbase) (hSum : bvk = A • Vbase + B • Rbase) :
    NontrivialRelation (F := F) Vbase Rbase :=
  ⟨Fin.elim0, A, B - bsk, Or.inr (Or.inl hA), by
    simp only [Fin.sum_univ_zero, zero_add]
    rw [smul_value_eq_smul_rand Vbase Rbase bvk A B bsk hExtract hSum, ← add_smul]
    have hc : (bsk - B) + (B - bsk) = (0 : F) := by ring
    rw [hc, zero_smul]⟩

/-! ### Integer balance: range / no-overflow lift

The binding reduction concludes `A = 0` in `F = ZMod r` (or computes a discrete-log
relation via `NontrivialRelation.ofImbalance`), i.e. balance *modulo the scalar-field order*.
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
`NontrivialRelation.ofBundleIntImbalance`.
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

The hypothesis `bvk = A • Vbase + B • Rbase` consumed above is not an assumption: it can be derived
from the value commitment `cv v rcv = v • Vbase + rcv • Rbase` being `F`-linear in `(v, rcv)`,
and the shape of a bundle — lists of spend / output `(value, randomness)` pairs together
with the declared `vBalance`. -/

/-- The value commitment `cv v rcv = v • Vbase + rcv • Rbase`. -/
def valueCommit (Vbase Rbase : M) (v rcv : F) : M := v • Vbase + rcv • Rbase

/-- A sum of value commitments decomposes as the value-sum times `Vbase` plus the randomness-sum
times `Rbase`. `•` distributes over the value and randomness sums. -/
theorem sum_valueCommit (Vbase Rbase : M) (l : List (F × F)) :
    (l.map fun p => valueCommit Vbase Rbase p.1 p.2).sum
      = (l.map Prod.fst).sum • Vbase + (l.map Prod.snd).sum • Rbase := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simp only [valueCommit, add_smul]
    abel

/-- The binding verification key of a bundle: `bvk = (∑ spend cv) − (∑ output cv) − v_balance • Vbase`. -/
def bindingVK (Vbase Rbase : M) (spends outputs : List (F × F)) (vBalance : F) : M :=
  (spends.map fun p => valueCommit Vbase Rbase p.1 p.2).sum
    - (outputs.map fun p => valueCommit Vbase Rbase p.1 p.2).sum - vBalance • Vbase

/-- **`hSum`, derived.** The binding verification key decomposes linearly as `A • Vbase + B • Rbase`,
with `A` the net value (`∑ spend values − ∑ output values − vBalance`) and `B` the net randomness
(`∑ spend randomness − ∑ output randomness`). -/
theorem bindingVK_decomp (Vbase Rbase : M) (spends outputs : List (F × F)) (vBalance : F) :
    bindingVK Vbase Rbase spends outputs vBalance
      = ((spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance) • Vbase
        + ((spends.map Prod.snd).sum - (outputs.map Prod.snd).sum) • Rbase := by
  rw [bindingVK, sum_valueCommit, sum_valueCommit]
  simp only [sub_smul]
  abel

/-- **Bundle balance reduction (field level), as a computed relation.** For a bundle whose
binding signature verifies (`hExtract`, from RedDSA extractability) and whose net value does
not balance modulo the scalar-field order, compute the nontrivial relation. There is no
binding assumption; the decomposition is derived by `bindingVK_decomp`. -/
def NontrivialRelation.ofBundleModImbalance (Vbase Rbase : M) (spends outputs : List (F × F))
    (vBalance bsk : F)
    (hne : (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance ≠ 0)
    (hExtract : bindingVK Vbase Rbase spends outputs vBalance = bsk • Rbase) :
    NontrivialRelation (F := F) Vbase Rbase :=
  NontrivialRelation.ofImbalance Vbase Rbase (bindingVK Vbase Rbase spends outputs vBalance) _ _ bsk hne hExtract
    (bindingVK_decomp Vbase Rbase spends outputs vBalance)

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

/-- **Integer balance reduction, as a computed relation** — the second half of the spec §4.13 /
§4.14 argument, over a bundle whose values are the actual integer note / net values (`ℤ`), with
field randomness. Given the no-overflow bound `hbound` and integer imbalance, compute the
nontrivial relation. There is no binding assumption — the computed relation is discharged against
DLR hardness at the computational layer, and "the bundle balances over ℤ" is the contrapositive.

The integer→field cast is derived using `castBundle_fst_sum`; the only added input over the field
reduction is the no-overflow bound `hbound`, provided by protocol-specific value-type range proofs
(`BindingSignature.Orchard.orchard_natAbs_lt` and `BindingSignature.Sapling.sapling_natAbs_lt`). -/
def NontrivialRelation.ofBundleIntImbalance {r : ℕ} [Fact (Nat.Prime r)]
    {M : Type*} [AddCommGroup M] [Module (ZMod r) M]
    (Vbase Rbase : M) (spends outputs : List (ℤ × ZMod r)) (vBalance : ℤ) (bsk : ZMod r)
    (hne : (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance ≠ 0)
    (hbound : ((spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance).natAbs < r)
    (hExtract : bindingVK Vbase Rbase (castBundle spends) (castBundle outputs) (vBalance : ZMod r) = bsk • Rbase) :
    NontrivialRelation (F := ZMod r) Vbase Rbase :=
  haveI : NeZero r := ⟨(Fact.out : Nat.Prime r).pos.ne'⟩
  have hne' : ((castBundle spends).map Prod.fst).sum - ((castBundle outputs).map Prod.fst).sum
      - (vBalance : ZMod r) ≠ 0 := fun hmod => by
    refine hne (intBalance_eq_zero_of_lt _ ?_ hbound)
    rw [castBundle_fst_sum, castBundle_fst_sum] at hmod
    rw [Int.cast_sub, Int.cast_sub]
    exact hmod
  NontrivialRelation.ofBundleModImbalance Vbase Rbase (castBundle spends) (castBundle outputs)
    (vBalance : ZMod r) bsk hne' hExtract

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
