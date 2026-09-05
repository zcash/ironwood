import Zcash.Security.Ledger.Bridge
import Zcash.Security.Ledger.Pool
import Zcash.Common.DiscreteLogRelation

/-!
# The games-facing Sinsemilla discrete-log-relation object

The onward reduction step for the classified Action escapes: a plain `def`
converting an `ActionBreakData` — the site and escape datum computed by
`classifyAction` — into a one-point `NontrivialRelation`, the games-facing
discrete-log-relation break among the Orchard-protocol Sinsemilla generator table and
the escaped site's domain point.  This is protocol-spec Theorem 5.4.4 made
computational end to end: the coefficients of the relation are read off the break
datum's consumed prefix (`breakCoeffs`), and its `Prop` fields are discharged from
`ValidBreak` alone.

The mathematical content is the chain-combination lemma `ofPoint_hashToPoint`: a
defined Sinsemilla chain value is the explicit generator combination
`2^n • Q + ∑ⱼ 2^(n−1−j) • S(mⱼ)` in the Pallas group.  Substituting it into the
resolved escape equation of a `ValidBreak` yields, for every escape kind, a linear
relation whose `Q`-coefficient is a power of two — nonzero in the odd-order scalar
field — or, for a `genZero` escape, a bare identity generator with coefficient one.

Like `classifyAction`, everything data-producing here is a plain compiled `def`
(`assert_computable … +choice` in `BridgeTests`): `Classical.choice` enters only
through erased `Prop` fields.
-/

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Circuits.Action.Circuit
open Zcash.Circuits.Specs (K)
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Pool

/-! ## The lifted generator table -/

/-- The Orchard-protocol Sinsemilla generator table, lifted into the Pallas group.
Total on `ℕ` for convenient use under chunk lists; off-table indices (never produced
by a `K`-bit chunk) map to the identity. -/
def pallasSAt (m : ℕ) : PallasGroup :=
  if h : m < 2 ^ K then
    PallasGroup.ofPoint (orchardGenerators.S m) (orchardGenerators.valid h)
  else 0

/-- The generator family of the discrete-log-relation object: the table restricted
to its index range. -/
def pallasS (t : Fin (2 ^ K)) : PallasGroup := pallasSAt t.1

theorem pallasSAt_of_lt {m : ℕ} (h : m < 2 ^ K) :
    pallasSAt m =
      PallasGroup.ofPoint (orchardGenerators.S m) (orchardGenerators.valid h) :=
  dif_pos h

/-! ## The combined deployed basis -/

/-- The `CommitIvk` domain point `Q("z.cash:Orchard-CommitIvk-M")`, as a group element. -/
def ivkQpt : PallasGroup := PallasGroup.ofPoint Pool.ivkQ (Or.inl Pool.ivkQ_onCurve)

/-- The `CommitIvk` randomness base, as a group element — the `commitIvkR` argument of
the Orchard-protocol `keyBinding` interface. -/
def commitIvkRpt : PallasGroup :=
  PallasGroup.ofPoint Ecc.MulFixed.Certs.commitIvkR.point
    (Or.inl Ecc.MulFixed.Certs.commitIvkR.onCurve)

/-- The `NoteCommit` domain point `Q("z.cash:Orchard-NoteCommit-M")`, as a group
element. -/
def noteQpt : PallasGroup := PallasGroup.ofPoint Pool.noteQ (Or.inl Pool.noteQ_onCurve)

/-- The `NoteCommit` randomness base, as a group element. -/
def noteCommitRpt : PallasGroup :=
  PallasGroup.ofPoint Ecc.MulFixed.Certs.noteCommitR.point
    (Or.inl Ecc.MulFixed.Certs.noteCommitR.onCurve)

/-- The Merkle domain point `Q("z.cash:Orchard-MerkleCRH")`, as a group element. -/
def merkleQpt : PallasGroup := PallasGroup.ofPoint Pool.merkleQ (Or.inl Pool.merkleQ_onCurve)

/-- The named slots of the combined deployed basis's distinguished points. The `idx`
prefix keeps the slot names apart from the points they refer to. -/
inductive OrchardPointIndex where
  | idxIvkQ
  | idxCommitIvkR
  | idxNoteQ
  | idxNoteCommitR
  | idxMerkleQ
  | idxValueCommitV
  | idxValueCommitR
  deriving DecidableEq

instance : Fintype OrchardPointIndex :=
  ⟨⟨[OrchardPointIndex.idxIvkQ, .idxCommitIvkR, .idxNoteQ, .idxNoteCommitR, .idxMerkleQ,
      .idxValueCommitV, .idxValueCommitR], by decide⟩,
    fun x => by cases x <;> decide⟩

/-- **The combined deployed basis's distinguished points.** Every relation arm of the
Balance route lands among the Sinsemilla generator table and these seven deployed
points: the three Sinsemilla domain points, their two commitment randomness bases, and
the two value-commitment bases. -/
def orchardPoints : OrchardPointIndex → PallasGroup
  | .idxIvkQ => ivkQpt
  | .idxCommitIvkR => commitIvkRpt
  | .idxNoteQ => noteQpt
  | .idxNoteCommitR => noteCommitRpt
  | .idxMerkleQ => merkleQpt
  | .idxValueCommitV => valueCommitV
  | .idxValueCommitR => valueCommitR

/-- Embed a relation over the generator table and a sub-vector of the deployed points
into the combined basis: the table slots map identically, and each distinguished slot
maps to its `orchardPoints` slot. -/
def toOrchardPoints {s : ℕ} {V : Fin s → PallasGroup}
    (w : NontrivialRelation (F := Fq) pallasS V) (g : Fin s → OrchardPointIndex)
    (gr : OrchardPointIndex → Option (Fin s)) (hg : Function.IsPartialInv g gr)
    (hpt : ∀ i, orchardPoints (g i) = V i) :
    NontrivialRelation (F := Fq) pallasS orchardPoints :=
  w.embed (Sum.map id g) (sumMapPartialInv gr) (isPartialInv_sumMap_id hg)
    (by rintro (a | i)
        · rfl
        · exact hpt i)

/-! ## The chain-combination lemma -/

/-- One chain step in the Pallas group: a defined double-and-add step maps
`acc ↦ 2·acc + S(m)`. -/
private theorem ofPointChain_step {m : ℕ} (hm : m < 2 ^ K) {Q Q' : Point Fp}
    (hQ : Q.Valid) (hQ' : Q'.Valid)
    (hs : step orchardGenerators.S m Q = some Q') :
    PallasGroup.ofPoint Q' hQ' = 2 • PallasGroup.ofPoint Q hQ + pallasSAt m := by
  have hSm : (orchardGenerators.S m).Valid := orchardGenerators.valid hm
  have eq : Q' = (Q + orchardGenerators.S m) + Q := by
    simp only [step, Point.doubleAndAdd, Option.bind_eq_bind] at hs
    by_cases hc₁ : Q = 0 ∨ orchardGenerators.S m = 0 ∨ Q.x = (orchardGenerators.S m).x
    · rw [Point.incompleteAdd_def, if_pos hc₁] at hs; simp at hs
    rw [Point.incompleteAdd_def, if_neg hc₁] at hs
    rw [show ((some (Q + orchardGenerators.S m)).bind fun t => Point.incompleteAdd t Q)
      = Point.incompleteAdd (Q + orchardGenerators.S m) Q from rfl] at hs
    by_cases hc₂ : Q + orchardGenerators.S m = 0 ∨ Q = 0 ∨ (Q + orchardGenerators.S m).x = Q.x
    · rw [Point.incompleteAdd_def, if_pos hc₂] at hs; simp at hs
    rw [Point.incompleteAdd_def, if_neg hc₂] at hs
    exact (Option.some.inj hs).symm
  subst eq
  show PallasGroup.ofPoint ((Q + orchardGenerators.S m) + Q)
      (Point.valid_add (Point.valid_add hQ hSm) hQ) = 2 • PallasGroup.ofPoint Q hQ + pallasSAt m
  rw [PallasGroup.ofPoint_add (Point.valid_add hQ hSm) hQ,
    PallasGroup.ofPoint_add hQ hSm, pallasSAt_of_lt hm, two_nsmul]
  abel

/-- The chain-combination lemma, in the `∀`-form convenient for forward induction. -/
private theorem ofPointChain_hash : ∀ (chunks : List ℕ) {Q acc : Point Fp} (hQ : Q.Valid),
    (∀ m ∈ chunks, m < 2 ^ K) →
    hashToPoint orchardGenerators.S Q chunks = some acc → ∀ (hacc : acc.Valid),
    PallasGroup.ofPoint acc hacc =
      2 ^ chunks.length • PallasGroup.ofPoint Q hQ +
        ∑ j ∈ Finset.range chunks.length,
          2 ^ (chunks.length - 1 - j) • pallasSAt (chunks.getD j 0) := by
  intro chunks
  induction chunks with
  | nil =>
    intro Q acc hQ hb h hacc
    rw [hashToPoint_nil, Option.some.injEq] at h
    subst h
    simp only [List.length_nil, pow_zero, one_smul, Finset.range_zero, Finset.sum_empty, add_zero]
  | cons m rest ih =>
    intro Q acc hQ hb h hacc
    cases hs : step orchardGenerators.S m Q with
    | none =>
      rw [hashToPoint_cons, hs] at h
      simp at h
    | some Q' =>
      have h' : hashToPoint orchardGenerators.S Q' rest = some acc := by
        rw [hashToPoint_cons, hs] at h; exact h
      have hm : m < 2 ^ K := hb m (by simp)
      have hQ' : Q'.Valid := step_valid hQ hm hs
      have hbrest : ∀ k ∈ rest, k < 2 ^ K := fun k hk => hb k (List.mem_cons_of_mem m hk)
      have IH := ih hQ' hbrest h' hacc
      rw [IH, ofPointChain_step hm hQ hQ' hs]
      simp only [List.length_cons]
      rw [Finset.sum_range_succ', List.getD_cons_zero]
      have hsum : ∑ j ∈ Finset.range rest.length,
            2 ^ (rest.length + 1 - 1 - (j + 1)) • pallasSAt ((m :: rest).getD (j + 1) 0)
          = ∑ j ∈ Finset.range rest.length,
            2 ^ (rest.length - 1 - j) • pallasSAt (rest.getD j 0) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [List.getD_cons_succ,
          show rest.length + 1 - 1 - (j + 1) = rest.length - 1 - j from by omega]
      rw [hsum, show rest.length + 1 - 1 - 0 = rest.length from by omega,
        pow_succ, mul_smul, smul_add]
      abel

/-- A defined Sinsemilla chain value is the explicit generator combination
`2^n • Q + ∑ⱼ 2^(n−1−j) • S(mⱼ)` (`n = chunks.length`), in the Pallas group.  This
is the "explicit combination" reading of the honest prefix chain used informally by
`ValidBreak`'s documentation, now as a theorem. -/
theorem ofPoint_hashToPoint {Q acc : Point Fp} (hQ : Q.Valid) {chunks : List ℕ}
    (hb : ∀ m ∈ chunks, m < 2 ^ K)
    (h : hashToPoint orchardGenerators.S Q chunks = some acc) (hacc : acc.Valid) :
    PallasGroup.ofPoint acc hacc =
      2 ^ chunks.length • PallasGroup.ofPoint Q hQ +
        ∑ j ∈ Finset.range chunks.length,
          2 ^ (chunks.length - 1 - j) • pallasSAt (chunks.getD j 0) :=
  ofPointChain_hash chunks hQ hb h hacc

/-! ## Relation coefficients -/

/-- The table coefficient contributed by the consumed prefix `l`: generator `t`
receives `2^(n−1−j)` for every position `j` of `l` holding chunk value `t`. -/
def preCoeffs (l : List ℕ) (t : Fin (2 ^ K)) : Fq :=
  ∑ j ∈ Finset.range l.length,
    if l.getD j 0 = t.1 then (2 : Fq) ^ (l.length - 1 - j) else 0

/-- The indicator coefficient vector of a single table generator. -/
def indicator (c t : Fin (2 ^ K)) : Fq := if t = c then 1 else 0

/-- The escape chunk as a table index.  The reduction only consumes it under the
`< 2^K` bound of the real query families, where the reduction is the identity. -/
def chunkIdx (br : BreakData) : Fin (2 ^ K) :=
  ⟨br.chunk % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩

theorem chunkIdx_of_lt {br : BreakData} (h : br.chunk < 2 ^ K) :
    (chunkIdx br).1 = br.chunk :=
  Nat.mod_eq_of_lt h

private theorem coeffs_two_ne_zero : (2 : Fq) ≠ 0 := by
  intro h
  have hdvd : (CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD : ℕ) ∣ 2 := by
    have : ((2 : ℕ) : Fq) = 0 := by exact_mod_cast h
    exact (ZMod.natCast_eq_zero_iff 2 _).mp this
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  revert hle
  norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]

/-- Scalar-field power-of-two coefficients act as the corresponding natural
multiplicities. -/
theorem two_pow_smul_eq_nsmul (e : ℕ) (P : PallasGroup) :
    (2 : Fq) ^ e • P = 2 ^ e • P := by
  have : (2 : Fq) ^ e = ((2 ^ e : ℕ) : Fq) := by push_cast; ring
  rw [this, Nat.cast_smul_eq_nsmul]

/-- Powers of two are nonzero in the odd-order Pallas scalar field — the
nontriviality witness for every escape kind with an honest prefix chain. -/
theorem two_pow_ne_zero (e : ℕ) : ((2 : Fq) ^ e) ≠ 0 :=
  pow_ne_zero e coeffs_two_ne_zero

/-- Summing the prefix coefficients against the table recovers the prefix's own
generator sum. -/
theorem sum_preCoeffs_smul {l : List ℕ} (hb : ∀ m ∈ l, m < 2 ^ K) :
    ∑ t : Fin (2 ^ K), preCoeffs l t • pallasS t =
      ∑ j ∈ Finset.range l.length,
        (2 : Fq) ^ (l.length - 1 - j) • pallasSAt (l.getD j 0) := by
  simp only [preCoeffs, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < l.length := Finset.mem_range.mp hj
  have hbound : l.getD j 0 < 2 ^ K := by
    apply hb
    rw [List.getD_eq_getElem l 0 hjlt]
    exact List.getElem_mem _
  rw [Finset.sum_eq_single (⟨l.getD j 0, hbound⟩ : Fin (2 ^ K))]
  · simp [pallasS]
  · intro t _ hne
    rw [if_neg, zero_smul]
    intro heq
    exact hne (Fin.ext heq.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Summing an indicator against the table picks out its generator. -/
theorem sum_indicator_smul (c : Fin (2 ^ K)) :
    ∑ t : Fin (2 ^ K), indicator c t • pallasS t = pallasS c := by
  simp only [indicator, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

/-! ## The coefficients of a break datum -/

/-- The relation coefficients `(a, α)` computed from a break datum: the table
vector and the domain-point coefficient of the escape's resolved point equation,
after substituting the prefix chain's explicit generator combination.  Data only —
correctness is `breakCoeffs_relation`, nontriviality `breakCoeffs_nontrivial`. -/
def breakCoeffs (br : BreakData) : (Fin (2 ^ K) → Fq) × Fq :=
  match br.kind with
  | .accZero => (preCoeffs br.pre, 2 ^ br.pre.length)
  | .genZero => (indicator (chunkIdx br), 0)
  | .collision neg =>
      (fun t => preCoeffs br.pre t + (if neg then 1 else -1) * indicator (chunkIdx br) t,
        2 ^ br.pre.length)
  | .sumZero =>
      (fun t => preCoeffs br.pre t + indicator (chunkIdx br) t, 2 ^ br.pre.length)
  | .doubleCollision =>
      (fun t => 2 * preCoeffs br.pre t + indicator (chunkIdx br) t,
        2 ^ (br.pre.length + 1))

/-- The computed coefficients are never all zero: every kind but `genZero` carries
the power-of-two domain coefficient, and `genZero`'s table vector is an
indicator. -/
theorem breakCoeffs_nontrivial (br : BreakData) :
    (breakCoeffs br).1 ≠ 0 ∨ (breakCoeffs br).2 ≠ 0 := by
  rcases hbr : br.kind with _ | _ | neg | _ | _ <;>
    simp only [breakCoeffs, hbr]
  · exact Or.inr (two_pow_ne_zero _)
  · refine Or.inl ?_
    intro h
    have := congrFun h (chunkIdx br)
    simp only [indicator, if_pos, Pi.zero_apply] at this
    exact one_ne_zero this
  · exact Or.inr (two_pow_ne_zero _)
  · exact Or.inr (two_pow_ne_zero _)
  · exact Or.inr (two_pow_ne_zero _)

/-- **Correctness of the computed coefficients**: for a valid break of a bounded
query, the coefficients satisfy the discrete-log relation in the Pallas group. -/
theorem breakCoeffs_relation {Qpt : Point Fp} (hQ : Qpt.Valid) {br : BreakData}
    (hvb : ValidBreak orchardGenerators.S Qpt br)
    (hpre : ∀ m ∈ br.pre, m < 2 ^ K) (hchunk : br.chunk < 2 ^ K) :
    (∑ t : Fin (2 ^ K), (breakCoeffs br).1 t • pallasS t) +
      (breakCoeffs br).2 • PallasGroup.ofPoint Qpt hQ = 0 := by
  obtain ⟨hchain, hPointEq⟩ := hvb
  have hacc : br.acc.Valid :=
    hashToPoint_valid_of_mem hQ (fun m hm => orchardGenerators.valid (hpre m hm)) hchain
  -- The prefix chain as the explicit table combination, in the reduction's coefficients.
  have hAcc : PallasGroup.ofPoint br.acc hacc =
      2 ^ br.pre.length • PallasGroup.ofPoint Qpt hQ +
        ∑ t : Fin (2 ^ K), preCoeffs br.pre t • pallasS t := by
    rw [sum_preCoeffs_smul hpre, ofPoint_hashToPoint hQ hpre hchain hacc]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => (two_pow_smul_eq_nsmul _ _).symm)
  -- The escape chunk generator, as a table element.
  have hSC : pallasS (chunkIdx br) =
      PallasGroup.ofPoint (orchardGenerators.S br.chunk) (orchardGenerators.valid hchunk) := by
    show pallasSAt (chunkIdx br).1 = _
    rw [chunkIdx_of_lt hchunk, pallasSAt_of_lt hchunk]
  cases hkind : br.kind with
  | accZero =>
    simp only [BreakData.PointEq, hkind] at hPointEq
    have hA0 : PallasGroup.ofPoint br.acc hacc = 0 :=
      PallasGroup.ofPoint_eq_zero hacc hPointEq
    rw [hAcc] at hA0
    simp only [breakCoeffs, hkind]
    rw [two_pow_smul_eq_nsmul, ← hA0]
    abel
  | genZero =>
    simp only [BreakData.PointEq, hkind] at hPointEq
    simp only [breakCoeffs, hkind]
    rw [sum_indicator_smul, zero_smul, add_zero, hSC]
    exact PallasGroup.ofPoint_eq_zero (orchardGenerators.valid hchunk) hPointEq
  | collision neg =>
    simp only [BreakData.PointEq, hkind] at hPointEq
    simp only [breakCoeffs, hkind]
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, sum_indicator_smul, two_pow_smul_eq_nsmul]
    cases neg with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hPointEq ⊢
      have hAeq : PallasGroup.ofPoint br.acc hacc = pallasS (chunkIdx br) := by
        rw [hSC]; exact lift_eq_of_point_eq hacc (orchardGenerators.valid hchunk) hPointEq
      rw [hAcc] at hAeq
      rw [neg_one_smul, ← hAeq]
      abel
    | true =>
      simp only [if_true] at hPointEq ⊢
      have hAeq : PallasGroup.ofPoint br.acc hacc = -pallasS (chunkIdx br) := by
        rw [hSC, ← PallasGroup.ofPoint_neg (orchardGenerators.valid hchunk)]
        exact lift_eq_of_point_eq hacc _ hPointEq
      rw [hAcc] at hAeq
      rw [one_smul]
      have hz : 2 ^ br.pre.length • PallasGroup.ofPoint Qpt hQ +
          (∑ t : Fin (2 ^ K), preCoeffs br.pre t • pallasS t) + pallasS (chunkIdx br) = 0 := by
        rw [hAeq]; abel
      rw [← hz]; abel
  | sumZero =>
    simp only [BreakData.PointEq, hkind] at hPointEq
    simp only [breakCoeffs, hkind]
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib, sum_indicator_smul, two_pow_smul_eq_nsmul]
    have hKind0 : PallasGroup.ofPoint br.acc hacc + pallasS (chunkIdx br) = 0 := by
      rw [hSC, ← PallasGroup.ofPoint_add hacc (orchardGenerators.valid hchunk)]
      exact PallasGroup.ofPoint_eq_zero _ hPointEq
    rw [hAcc] at hKind0
    rw [← hKind0]; abel
  | doubleCollision =>
    simp only [BreakData.PointEq, hkind] at hPointEq
    simp only [breakCoeffs, hkind]
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, sum_indicator_smul, two_pow_smul_eq_nsmul]
    have h2Pre := two_pow_smul_eq_nsmul 1 (∑ t : Fin (2 ^ K), preCoeffs br.pre t • pallasS t)
    simp only [pow_one] at h2Pre
    rw [h2Pre]
    have hKind0 : (2 : ℕ) • PallasGroup.ofPoint br.acc hacc + pallasS (chunkIdx br) = 0 := by
      rw [hSC, ← PallasGroup.ofPoint_nsmul 2 br.acc hacc,
        ← PallasGroup.ofPoint_add (Point.valid_nsmul hacc 2) (orchardGenerators.valid hchunk)]
      exact PallasGroup.ofPoint_eq_zero _ hPointEq
    rw [hAcc, smul_add, smul_smul] at hKind0
    rw [pow_succ, mul_comm (2 ^ br.pre.length) 2, ← hKind0]
    abel

/-- Package a valid bounded break as the games-facing relation object. The coefficients
are the computed `breakCoeffs`; the `Prop` obligations are discharged from the break's
validity alone. -/
def relationOfValidBreak {Qpt : Point Fp} (hQ : Qpt.Valid) (br : BreakData)
    (hvb : ValidBreak orchardGenerators.S Qpt br)
    (hpre : ∀ m ∈ br.pre, m < 2 ^ K) (hchunk : br.chunk < 2 ^ K) :
    NontrivialRelation (F := Fq) pallasS ![PallasGroup.ofPoint Qpt hQ] :=
  NontrivialRelation.ofParts (breakCoeffs br).1 ![(breakCoeffs br).2]
    (by
      rcases breakCoeffs_nontrivial br with ha | hα
      · exact Or.inl ha
      · exact Or.inr (Function.ne_iff.mpr ⟨0, by simpa using hα⟩))
    (by
      have h := breakCoeffs_relation hQ hvb hpre hchunk
      simpa [commitGen, Fin.sum_univ_one] using h)

/-! ## Site dispatch

The classifier records which of the four query families escaped; each site fixes a
domain point and the witness's exact query at that site.  These dispatchers are
shared by the conversion and its correctness statement, so the produced relation is
tied to the same query the classifier evaluated. -/

/-- The domain point of a break site. -/
def siteQ : BreakSite → Point Fp
  | .commitIvk => orchardBases.ivkQ
  | .noteCommitOld => orchardBases.noteQ
  | .noteCommitNew => orchardBases.noteQ
  | .merkle _ => orchardBases.merkleQ

theorem siteQ_valid (s : BreakSite) : (siteQ s).Valid := by
  cases s with
  | commitIvk => exact .inl orchardBases.ivkQ_onCurve
  | noteCommitOld => exact .inl orchardBases.noteQ_onCurve
  | noteCommitNew => exact .inl orchardBases.noteQ_onCurve
  | merkle _ => exact .inl orchardBases.merkleQ_onCurve

/-- The domain point of a break site, in the Pallas group. -/
def sitePoint (s : BreakSite) : PallasGroup :=
  PallasGroup.ofPoint (siteQ s) (siteQ_valid s)

/-- The witness's exact Sinsemilla query at a break site. -/
def siteQuery (wit : ActionData) : BreakSite → List ℕ
  | .commitIvk => ivkQuery wit
  | .noteCommitOld => noteOldQuery wit
  | .noteCommitNew => noteNewQuery wit
  | .merkle i => merkleQuery wit i

/-- Every chunk of every site query indexes the generator table. -/
theorem siteQuery_bounded (wit : ActionData) (s : BreakSite) :
    ∀ m ∈ siteQuery wit s, m < 2 ^ K := by
  cases s with
  | commitIvk => intro m hm; exact chunksOf_mem_lt hm
  | noteCommitOld => intro m hm; exact chunksOf_mem_lt hm
  | noteCommitNew => intro m hm; exact chunksOf_mem_lt hm
  | merkle i =>
    intro m hm
    simp only [siteQuery, merkleQuery, merkleChunks, List.mem_map, List.mem_range] at hm
    obtain ⟨j, -, rfl⟩ := hm
    exact Nat.mod_lt _ (Nat.two_pow_pos K)

/-! ## From classified break data to the relation -/

/-- **Classifier inversion**: a classified escape is the escape of the witness's own
exact query at the recorded site. -/
theorem classify_query_inr {wit : ActionData} {abr : ActionBreakData}
    (h : classifyAction wit = some abr) :
    hashToPointB orchardGenerators.S (siteQ abr.site) (siteQuery wit abr.site) =
      .inr abr.data := by
  unfold classifyAction at h
  cases hivk : hashToPointB orchardGenerators.S Action.ivkQ (ivkQuery wit) with
  | inr brd =>
    simp only [hivk] at h
    injection h with h'; subst h'
    exact hivk
  | inl Bi =>
    simp only [hivk] at h
    cases hold : hashToPointB orchardGenerators.S Action.noteQ (noteOldQuery wit) with
    | inr brd =>
      simp only [hold] at h
      injection h with h'; subst h'
      exact hold
    | inl Bo =>
      simp only [hold] at h
      cases hnew : hashToPointB orchardGenerators.S Action.noteQ (noteNewQuery wit) with
      | inr brd =>
        simp only [hnew] at h
        injection h with h'; subst h'
        exact hnew
      | inl Bn =>
        simp only [hnew] at h
        unfold classifyMerkle at h
        obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some h
        cases hm : hashToPointB orchardGenerators.S Action.merkleQ (merkleQuery wit i) with
        | inl B => simp [hm] at hi
        | inr br =>
          simp only [hm] at hi
          injection hi with hi'; subst hi'
          exact hm

/-- The escape datum of a site query is bounded: its prefix and escape chunk are
chunks of the query itself. -/
theorem break_bounds {wit : ActionData} {s : BreakSite} {br : BreakData}
    (h : hashToPointB orchardGenerators.S (siteQ s) (siteQuery wit s) = .inr br) :
    (∀ m ∈ br.pre, m < 2 ^ K) ∧ br.chunk < 2 ^ K := by
  obtain ⟨hsplit, -, -⟩ := hashToPointB_inr h
  have hb := siteQuery_bounded wit s
  rw [hsplit] at hb
  exact ⟨fun m hm => hb m (List.mem_append_left _ hm),
    hb br.chunk (List.mem_append_right _ List.mem_cons_self)⟩

/-- The slot of a break site's domain point in the combined deployed basis. -/
def siteSlot : BreakSite → OrchardPointIndex
  | .commitIvk => .idxIvkQ
  | .noteCommitOld => .idxNoteQ
  | .noteCommitNew => .idxNoteQ
  | .merkle _ => .idxMerkleQ

/-- Each break site's combined slot holds its domain point. -/
theorem orchardPoints_siteSlot (s : BreakSite) : orchardPoints (siteSlot s) = sitePoint s := by
  cases s <;> rfl

/-- **Reduction from a classified `ActionBreakData` into the games-facing
discrete-log-relation** at the escaped site's domain point.  The hypothesis ties the
datum to the witness's own query; `classify_query_inr` discharges it for the
classifier's output. -/
def relationOfBreakData (wit : ActionData) (abr : ActionBreakData)
    (h : hashToPointB orchardGenerators.S (siteQ abr.site) (siteQuery wit abr.site) =
      .inr abr.data) :
    NontrivialRelation (F := Fq) pallasS orchardPoints :=
  toOrchardPoints
    (relationOfValidBreak (siteQ_valid abr.site) abr.data
      (validBreak_of_inr (siteQ_valid abr.site)
        (fun m hm => orchardGenerators.S_onCurve (siteQuery_bounded wit abr.site m hm)) h)
      (break_bounds h).1 (break_bounds h).2)
    (fun _ => siteSlot abr.site) (fun j => if j = siteSlot abr.site then some 0 else none)
    (isPartialInv_const_slot _)
    (fun i => by fin_cases i; exact orchardPoints_siteSlot abr.site)

/-- A classified Action escape reduced onward: the site together with a nontrivial
discrete-log relation among the Orchard-protocol generator table and the combined
deployed points, with the coefficients supported on the escaped site's domain-point
slot. -/
structure ActionDLBreak where
  site : BreakSite
  rel : NontrivialRelation (F := Fq) pallasS orchardPoints

/-- End-to-end computable reduction at the Action boundary: classify the witness's
four query families and reduce the first escape to its discrete-log relation. -/
def classifyRelation (wit : ActionData) : Option ActionDLBreak :=
  match h : classifyAction wit with
  | none => none
  | some abr => some ⟨abr.site, relationOfBreakData wit abr (classify_query_inr h)⟩

/-- The reduction succeeds exactly when the classifier reports an escape. -/
theorem classifyRelation_isSome_iff (wit : ActionData) :
    (classifyRelation wit).isSome ↔ (classifyAction wit).isSome := by
  unfold classifyRelation
  split <;> simp_all

/-- The site of the classifier escape behind a successful reduction: the site of
the computed `classifyAction` value, whose definedness is recovered through
`classifyRelation_isSome_iff`. -/
def classifierSiteOf (wit : ActionData) {dlb : ActionDLBreak}
    (h : classifyRelation wit = some dlb) : BreakSite :=
  ((classifyAction wit).get
    ((classifyRelation_isSome_iff wit).mp
      (Option.isSome_iff_exists.mpr ⟨dlb, h⟩))).site

/-- The reduction reports the classifier's own site. -/
theorem classifyRelation_site {wit : ActionData} {dlb : ActionDLBreak}
    (h : classifyRelation wit = some dlb) :
    dlb.site = classifierSiteOf wit h := by
  obtain ⟨abr, heq, hsite⟩ :
      ∃ abr, classifyAction wit = some abr ∧ dlb.site = abr.site := by
    have h' := h
    unfold classifyRelation at h'
    split at h'
    · exact absurd h' (by simp)
    · next abr heq => exact ⟨abr, heq, by injection h' with h''; rw [← h'']⟩
  rw [hsite]
  simp [classifierSiteOf, heq]

/-- **The computable Action-to-ledger bridge.**  Run the classifier on the combined
circuit witness: an escape reduces onward to its computed discrete-log relation, and
otherwise the refined ledger action — instance, witness, and the satisfaction
proofs — is returned as data (`ActionLedgerSuccess.ofSpec`). -/
def actionSpecToLedgerData {MSG SIG : Type*}
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    (input : PublicInputs Fp) (wit : PrivateWitness)
    (h : ActionSpec input wit) :
    ActionLedgerSuccess spendAuthVerify bindingVerify (combine input wit) ⊕'
      ActionDLBreak :=
  match hcl : classifyRelation (combine input wit) with
  | some dlb => .inr dlb
  | none => .inl (ActionLedgerSuccess.ofSpec spendAuthVerify bindingVerify input wit h
      (Option.not_isSome_iff_eq_none.mp fun hs => by
        have hrel := (classifyRelation_isSome_iff (combine input wit)).mpr hs
        rw [hcl] at hrel
        simp at hrel))

/-! ## The chain-collision reducer

Shared by every arm whose break compares two blinded Sinsemilla outputs: the
key-binding break compares two `Commit^ivk` openings, the note-commitment break two
note commitments, and a Merkle collision two compressions (with zero blinding). Two
defined chains at the same domain point whose blinded outputs agree up to sign
compute a relation among the table, the domain point, and the blinding base. -/

/-- A defined, blinded Sinsemilla chain as the explicit `(table, Q, W)`-combination
determined by its chunk list. -/
theorem blinded_chain_eq {Q : Point Fp} (hQ : Q.Valid) (W : PallasGroup)
    {l : List ℕ} (hb : ∀ m ∈ l, m < 2 ^ K)
    {p : Point Fp} (h : hashToPoint orchardGenerators.S Q l = some p) (hv : p.Valid)
    (r : Fq) :
    PallasGroup.ofPoint p hv + r • W =
      commitGen pallasS (preCoeffs l)
        + ((2 : Fq) ^ l.length) • PallasGroup.ofPoint Q hQ + r • W := by
  rw [ofPoint_hashToPoint hQ hb h hv]
  simp only [← two_pow_smul_eq_nsmul, commitGen]
  rw [sum_preCoeffs_smul hb]
  abel

/-- Every Pallas base-field value is below `2^255`: the field's order is. -/
theorem fp_val_lt (x : Fp) : x.val < 2 ^ 255 :=
  lt_trans (ZMod.val_lt x) (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])

/-- The `ℕ`-level chunk coefficients: generator `t` receives `2^(n−1−j)` for every
position `j` holding chunk value `t`, summed in `ℕ`. -/
def natCoeffs (l : List ℕ) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range l.length,
    if l.getD j 0 = t then 2 ^ (l.length - 1 - j) else 0

/-- The scalar-field coefficients are the `ℕ`-level coefficients, cast. -/
theorem preCoeffs_eq_natCoeffs (l : List ℕ) (t : Fin (2 ^ K)) :
    preCoeffs l t = ((natCoeffs l t.1 : ℕ) : Fq) := by
  simp [preCoeffs, natCoeffs, apply_ite (Nat.cast : ℕ → Fq)]

/-- Head decomposition of the `ℕ`-level coefficients. -/
theorem natCoeffs_cons (c : ℕ) (rest : List ℕ) (t : ℕ) :
    natCoeffs (c :: rest) t
      = (if c = t then 2 ^ rest.length else 0) + natCoeffs rest t := by
  simp only [natCoeffs, List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
    List.getD_cons_zero, Nat.add_sub_cancel, Nat.sub_zero]
  rw [Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have he : rest.length - (j + 1) = rest.length - 1 - j := by omega
  rw [he]

/-- The `ℕ`-level coefficients stay below `2^n`: the exponents are distinct. -/
theorem natCoeffs_lt (l : List ℕ) (t : ℕ) : natCoeffs l t < 2 ^ l.length := by
  induction l with
  | nil => simp [natCoeffs]
  | cons c rest ih =>
    rw [natCoeffs_cons, List.length_cons, pow_succ]
    split <;> omega

/-- **The `ℕ`-level coefficients determine the list** (same lengths): the head's
`2^n` term dominates the tail's `≤ 2^n − 1`, forcing head equality, and the tails
follow by cancellation. -/
theorem natCoeffs_inj : ∀ {l₁ l₂ : List ℕ}, l₁.length = l₂.length →
    (∀ t, natCoeffs l₁ t = natCoeffs l₂ t) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ hlen _
    exact (List.length_eq_zero_iff.mp hlen.symm).symm ▸ rfl
  | cons c₁ rest₁ ih =>
    intro l₂ hlen h
    obtain ⟨c₂, rest₂, rfl⟩ : ∃ c₂ rest₂, l₂ = c₂ :: rest₂ := by
      cases l₂ with
      | nil => simp at hlen
      | cons c₂ rest₂ => exact ⟨c₂, rest₂, rfl⟩
    have hrl : rest₁.length = rest₂.length := by simpa using hlen
    have hc : c₂ = c₁ := by
      by_contra hne
      have h₁ := h c₁
      rw [natCoeffs_cons, natCoeffs_cons, if_pos rfl, if_neg hne] at h₁
      have hb₂ := natCoeffs_lt rest₂ c₁
      rw [← hrl] at hb₂
      omega
    subst hc
    have htail : ∀ t, natCoeffs rest₁ t = natCoeffs rest₂ t := by
      intro t
      have ht := h t
      rw [natCoeffs_cons, natCoeffs_cons, hrl] at ht
      exact Nat.add_left_cancel ht
    rw [ih hrl htail]

/-- **The chunk coefficients determine the list** — the binary-expansion core of spec
Theorem 5.4.3, over the scalar field: for chunk lists of equal length at most 253, the
`ℕ`-level coefficient sums stay below the field order, so the cast is faithful and
`natCoeffs_inj` applies. -/
theorem preCoeffs_inj {l₁ l₂ : List ℕ}
    (hb₁ : ∀ m ∈ l₁, m < 2 ^ K) (hb₂ : ∀ m ∈ l₂, m < 2 ^ K)
    (hlen : l₁.length = l₂.length) (hn : l₁.length ≤ 253)
    (h : preCoeffs l₁ = preCoeffs l₂) : l₁ = l₂ := by
  refine natCoeffs_inj hlen fun t => ?_
  by_cases ht : t < 2 ^ K
  · have hcast := congrFun h ⟨t, ht⟩
    rw [preCoeffs_eq_natCoeffs, preCoeffs_eq_natCoeffs] at hcast
    have hlt : ∀ (l : List ℕ), l.length ≤ 253 →
        natCoeffs l t < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
      intro l hl
      calc natCoeffs l t < 2 ^ l.length := natCoeffs_lt l t
        _ ≤ 2 ^ 253 := Nat.pow_le_pow_right (by norm_num) hl
        _ < _ := by norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]
    have hv := congrArg ZMod.val hcast
    rwa [ZMod.val_natCast_of_lt (hlt l₁ hn), ZMod.val_natCast_of_lt (hlt l₂ (hlen ▸ hn))]
      at hv
  · -- Out-of-table values never occur in bounded lists, so both coefficients vanish.
    have hz : ∀ (l : List ℕ), (∀ m ∈ l, m < 2 ^ K) → natCoeffs l t = 0 := by
      intro l hbl
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjl : j < l.length := Finset.mem_range.mp hj
      have hmem : l.getD j 0 ∈ l := by
        rw [List.getD_eq_getElem _ _ hjl]
        exact List.getElem_mem _
      rw [if_neg]
      intro hEq
      exact ht (hEq ▸ hbl _ hmem)
    rw [hz l₁ hb₁, hz l₂ hb₂]

/-- **The chain-collision reducer.** Two defined Sinsemilla chains at the same domain
point, blinded by `r₁ • W` and `r₂ • W`, whose outputs agree up to sign, compute a
nontrivial relation among the table, the domain point, and `W` — provided the pair
`(chunk list, blinding scalar)` differs. The equality case rests on
`preCoeffs_inj` — chunk lists of length at most 253 are determined by their
coefficients, and every Orchard-protocol Sinsemilla message is far shorter. The
negation case is unconditional: the domain-point coefficients `2^n` and `-2^n` cannot
agree because `2^(n+1) ≠ 0` in the odd-order scalar field. -/
def relationOfChainPmEq {Q : Point Fp} (hQ : Q.Valid) {W : PallasGroup}
    {l₁ l₂ : List ℕ} (hb₁ : ∀ m ∈ l₁, m < 2 ^ K) (hb₂ : ∀ m ∈ l₂, m < 2 ^ K)
    (hlen : l₁.length = l₂.length)
    {p₁ p₂ : Point Fp}
    (h₁ : hashToPoint orchardGenerators.S Q l₁ = some p₁) (hv₁ : p₁.Valid)
    (h₂ : hashToPoint orchardGenerators.S Q l₂ = some p₂) (hv₂ : p₂.Valid)
    {r₁ r₂ : Fq}
    (heq : PallasGroup.ofPoint p₁ hv₁ + r₁ • W = PallasGroup.ofPoint p₂ hv₂ + r₂ • W ∨
      PallasGroup.ofPoint p₁ hv₁ + r₁ • W = -(PallasGroup.ofPoint p₂ hv₂ + r₂ • W))
    (hn : l₁.length ≤ 253)
    (hne : ¬(l₁ = l₂ ∧ r₁ = r₂)) :
    NontrivialRelation (F := Fq) pallasS ![PallasGroup.ofPoint Q hQ, W] :=
  if hplus : PallasGroup.ofPoint p₁ hv₁ + r₁ • W = PallasGroup.ofPoint p₂ hv₂ + r₂ • W then
    NontrivialRelation.ofCombinationCollision
      (a := preCoeffs l₁) (a' := preCoeffs l₂)
      (α := (2 : Fq) ^ l₁.length) (α' := (2 : Fq) ^ l₂.length)
      (β := r₁) (β' := r₂)
      (by
        have h := hplus
        rw [blinded_chain_eq hQ W hb₁ h₁ hv₁ r₁,
          blinded_chain_eq hQ W hb₂ h₂ hv₂ r₂] at h
        exact h)
      (by rintro ⟨ha, -, hr⟩; exact hne ⟨preCoeffs_inj hb₁ hb₂ hlen hn ha, hr⟩)
  else
    NontrivialRelation.ofCombinationCollision
      (a := preCoeffs l₁) (a' := -(preCoeffs l₂))
      (α := (2 : Fq) ^ l₁.length) (α' := -((2 : Fq) ^ l₂.length))
      (β := r₁) (β' := -r₂)
      (by
        have h := heq.resolve_left hplus
        rw [blinded_chain_eq hQ W hb₁ h₁ hv₁ r₁,
          blinded_chain_eq hQ W hb₂ h₂ hv₂ r₂] at h
        rw [h, commitGen_neg, neg_smul, neg_smul]
        abel)
      (by
        rintro ⟨-, hα, -⟩
        rw [hlen] at hα
        have h0 : (2 : Fq) ^ (l₂.length + 1) = 0 := by
          rw [pow_succ, mul_two]
          exact add_eq_zero_iff_eq_neg.mpr hα
        exact two_pow_ne_zero _ h0)


/-- With zero blinding scalars, the reducer's randomness-base coefficient is zero. -/
theorem relationOfChainPmEq_zero_beta {Q : Point Fp} (hQ : Q.Valid) {W : PallasGroup}
    {l₁ l₂ : List ℕ} (hb₁ : ∀ m ∈ l₁, m < 2 ^ K) (hb₂ : ∀ m ∈ l₂, m < 2 ^ K)
    (hlen : l₁.length = l₂.length)
    {p₁ p₂ : Point Fp}
    (h₁ : hashToPoint orchardGenerators.S Q l₁ = some p₁) (hv₁ : p₁.Valid)
    (h₂ : hashToPoint orchardGenerators.S Q l₂ = some p₂) (hv₂ : p₂.Valid)
    (heq : PallasGroup.ofPoint p₁ hv₁ + (0 : Fq) • W
        = PallasGroup.ofPoint p₂ hv₂ + (0 : Fq) • W ∨
      PallasGroup.ofPoint p₁ hv₁ + (0 : Fq) • W
        = -(PallasGroup.ofPoint p₂ hv₂ + (0 : Fq) • W))
    (hn : l₁.length ≤ 253) (hne : ¬(l₁ = l₂ ∧ (0 : Fq) = 0)) :
    (relationOfChainPmEq hQ hb₁ hb₂ hlen h₁ hv₁ h₂ hv₂ heq hn hne).β = 0 := by
  unfold relationOfChainPmEq
  split <;> simp [Zcash.NontrivialRelation.β,
    Zcash.NontrivialRelation.ofCombinationCollision,
    Zcash.NontrivialRelation.ofParts, augmentedCoeffs, BasisIndex.w]


end Zcash.Security.Ledger.Bridge
