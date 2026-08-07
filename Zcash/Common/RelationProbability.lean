import Zcash.Common.AlgebraicRelation
import Zcash.Common.UniformMeasure

/-!
# From relation probability to DL probability

Programming every basis slot converts a relation into a discrete log except on one `1/|F|`
hyperplane, so a relation finder is priced by the textbook single-generator DL advantage plus
`1/|F|` (`relation_prob_le_of_textbookDL`). The counting is over how the basis is sampled, not
over the finder: `A` is an arbitrary basis-indexed producer of relations, with no restriction on
how it computes one. Finder efficiency and finite-resource DLOG hardness remain premises.
-/

open scoped ENNReal

namespace Zcash

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

section Reduction
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype F] [DecidableEq F] (B : G)

/-- The public basis whose slot `i` is `s i • B`. -/
def scalarBasis (s : ι → F) : ι → G := fun i => s i • B

/-- The slot logs the reduction presents, for programming pairs `(x, y)` and challenge log `z`. -/
def programmedLogs (z : F) (x y : ι → F) : ι → F := fun i => x i + z * y i

omit [DecidableEq ι] [Nonempty ι] [Fintype F] in
/-- The presented basis carries its programming: slot `i` is `x i • B + y i • (z • B)`. -/
def programmedEmbedding (z : F) (x y : ι → F) :
    ProgrammedBasisEmbedding (F := F) B (z • B) (scalarBasis B (programmedLogs z x y)) :=
  { x := x
    y := y
    programmed := fun i => by
      simp [scalarBasis, programmedLogs, add_smul, mul_comm z (y i), mul_smul] }

variable (A : (b : ι → G) → Option (AlgebraicRelationWitness (F := F) b))

/-- Relation-finding event: on the presented basis, `A` returns a (nontrivial) relation. -/
def relSet : Finset (ι → F) :=
  Finset.univ.filter (fun s => (A (scalarBasis B s)).isSome)

/-! ### The programmed experiment

Reduction coins `(z, x, y)`: the challenge log and the two programming vectors. The finder runs on
the presented logs `programmedLogs z x y`. -/

/-- The coefficients of the relation returned on presented logs `s`; zero when none returns. -/
def returnedCoeffs (s : ι → F) : ι → F :=
  (A (scalarBasis B s)).elim 0 (fun r => r.coeffs)

omit [DecidableEq ι] [Nonempty ι] [Fintype F] [DecidableEq F] in
/-- `returnedCoeffs` reads off the coefficients of the relation actually returned. -/
theorem returnedCoeffs_of_eq_some {s : ι → F}
    {r : AlgebraicRelationWitness (F := F) (scalarBasis B s)}
    (hr : A (scalarBasis B s) = some r) :
    returnedCoeffs B A s = r.coeffs := by
  simp [returnedCoeffs, hr]

-- Genuinely noncomputable, in both halves: `Classical.arbitrary` is the only way to produce an
-- element of a type that is merely `Nonempty`, and `Exists.choose` the only way to read a slot out
-- of `exists_nonzero_coeff`. Neither is repairable by enumeration here — `Finset.toList` is itself
-- noncomputable (`Multiset.toList` goes through `Quot.out`), so `[Fintype ι]` supplies no list to
-- search. Making it computable would mean strengthening the interface to carry an explicit
-- enumeration, which the index type of a public basis has no reason to.
/-- A pivot slot where the returned relation has nonzero coefficient; arbitrary when none
returns. -/
noncomputable def pivotSlot (s : ι → F) : ι :=
  (A (scalarBasis B s)).elim (Classical.arbitrary ι) (fun r => r.exists_nonzero_coeff.choose)

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The pivot slot's coefficient is nonzero whenever a relation returns. -/
theorem returnedCoeffs_pivotSlot_ne_zero {s : ι → F}
    (hsome : (A (scalarBasis B s)).isSome) :
    returnedCoeffs B A s (pivotSlot B A s) ≠ 0 := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
  rw [returnedCoeffs_of_eq_some B A hr]
  simp only [pivotSlot, hr, Option.elim_some]
  exact r.exists_nonzero_coeff.choose_spec

/-- Programmed coins on which `A` returns a relation. -/
def programmedRelSet : Finset (F × (ι → F) × (ι → F)) :=
  Finset.univ.filter (fun t =>
    (A (scalarBasis B (programmedLogs t.1 t.2.1 t.2.2))).isSome)

/-- Winning coins: the returned relation's component against `y` is nonzero, so
`discreteLogOfChallenge_of_relation` computes the discrete log of `z • B`. -/
def winSet : Finset (F × (ι → F) × (ι → F)) :=
  Finset.univ.filter (fun t =>
    (A (scalarBasis B (programmedLogs t.1 t.2.1 t.2.2))).isSome ∧
      (∑ i, returnedCoeffs B A (programmedLogs t.1 t.2.1 t.2.2) i * t.2.2 i) ≠ 0)

/-- Failing coins: the returned relation annihilates the challenge programming `y`. -/
def missSet : Finset (F × (ι → F) × (ι → F)) :=
  Finset.univ.filter (fun t =>
    (A (scalarBasis B (programmedLogs t.1 t.2.1 t.2.2))).isSome ∧
      (∑ i, returnedCoeffs B A (programmedLogs t.1 t.2.1 t.2.2) i * t.2.2 i) = 0)

omit [Nonempty ι] in
/-- Every relation-producing programmed coin wins or lands in the annihilation hyperplane. -/
theorem programmedRelSet_subset_win_union_miss :
    programmedRelSet B A ⊆ winSet B A ∪ missSet B A := by
  intro t ht
  simp only [programmedRelSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  rcases eq_or_ne
      (∑ i, returnedCoeffs B A (programmedLogs t.1 t.2.1 t.2.2) i * t.2.2 i) 0 with h0 | h0
  · exact Finset.mem_union_right _ (by
      simp only [missSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ht, h0⟩)
  · exact Finset.mem_union_left _ (by
      simp only [winSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ht, h0⟩)

omit [Nonempty ι] [DecidableEq F] in
/-- Perfect simulation: for each honest log vector in the relation event, the programmed coins
hitting it are exactly the free choices of `(z, y)`. -/
theorem programmedRelSet_card :
    (programmedRelSet B A).card = (relSet B A).card * Fintype.card (F × (ι → F)) := by
  rw [← Finset.card_univ (α := F × (ι → F)), ← Finset.card_product]
  refine Finset.card_bij'
    (fun t _ => (programmedLogs t.1 t.2.1 t.2.2, (t.1, t.2.2)))
    (fun p _ => (p.2.1, fun i => p.1 i - p.2.1 * p.2.2 i, p.2.2))
    ?hi ?hj ?left ?right
  case hi =>
    rintro ⟨z, x, y⟩ ht
    simp only [programmedRelSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    simp only [relSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ht
  case hj =>
    rintro ⟨s, z, y⟩ hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true, relSet, Finset.mem_filter,
      true_and] at hp
    simp only [programmedRelSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hs : programmedLogs z (fun i => s i - z * y i) y = s := by
      funext i
      simp [programmedLogs]
    rw [hs]
    exact hp
  case left =>
    rintro ⟨z, x, y⟩ _
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    simp [programmedLogs]
  case right =>
    rintro ⟨s, z, y⟩ _
    simp only [Prod.mk.injEq, and_true]
    funext i
    simp [programmedLogs]

/-- Annihilation costs at most a `1/|F|` slice of the coins: stash the challenge log in the
returned relation's pivot slot of `y`, which the hyperplane equation recovers, so the coins embed
into one fewer field factor. -/
theorem missSet_card_le :
    (missSet B A).card ≤ Fintype.card ((ι → F) × (ι → F)) := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn
    (fun t => (programmedLogs t.1 t.2.1 t.2.2,
      Function.update t.2.2 (pivotSlot B A (programmedLogs t.1 t.2.1 t.2.2)) t.1))
    (fun _ _ => Finset.mem_univ _) ?_
  rintro ⟨z, x, y⟩ ht ⟨z', x', y'⟩ ht' heq
  simp only [Finset.mem_coe, missSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
  obtain ⟨hsome, hmiss⟩ := ht
  obtain ⟨hsome', hmiss'⟩ := ht'
  dsimp only at heq
  rw [Prod.mk.injEq] at heq
  obtain ⟨hs', hupd⟩ := heq
  have hs : programmedLogs z' x' y' = programmedLogs z x y := hs'.symm
  rw [hs] at hsome' hmiss' hupd
  set j := pivotSlot B A (programmedLogs z x y) with hj
  have hz : z = z' := by
    have := congrFun hupd j
    simpa [Function.update_self] using this
  have hyoff : ∀ i, i ≠ j → y i = y' i := by
    intro i hi
    have := congrFun hupd i
    simpa [Function.update_of_ne hi] using this
  have hcj : returnedCoeffs B A (programmedLogs z x y) j ≠ 0 :=
    returnedCoeffs_pivotSlot_ne_zero B A hsome
  have hyj : y j = y' j := by
    have h1 : returnedCoeffs B A (programmedLogs z x y) j * y j +
        ∑ i ∈ Finset.univ.erase j, returnedCoeffs B A (programmedLogs z x y) i * y i = 0 :=
      (Finset.add_sum_erase Finset.univ
        (fun i => returnedCoeffs B A (programmedLogs z x y) i * y i)
        (Finset.mem_univ j)).trans hmiss
    have h2 : returnedCoeffs B A (programmedLogs z x y) j * y' j +
        ∑ i ∈ Finset.univ.erase j, returnedCoeffs B A (programmedLogs z x y) i * y' i = 0 :=
      (Finset.add_sum_erase Finset.univ
        (fun i => returnedCoeffs B A (programmedLogs z x y) i * y' i)
        (Finset.mem_univ j)).trans hmiss'
    have herase : (∑ i ∈ Finset.univ.erase j,
          returnedCoeffs B A (programmedLogs z x y) i * y i)
        = ∑ i ∈ Finset.univ.erase j, returnedCoeffs B A (programmedLogs z x y) i * y' i :=
      Finset.sum_congr rfl fun i hi => by
        rw [hyoff i (Finset.ne_of_mem_erase hi)]
    rw [herase] at h1
    exact mul_left_cancel₀ hcj (add_right_cancel (h1.trans h2.symm))
  have hy : y = y' := by
    funext i
    rcases eq_or_ne i j with hi | hi
    · rw [hi]; exact hyj
    · exact hyoff i hi
  have hx : x = x' := by
    funext i
    have := congrFun hs.symm i
    simp only [programmedLogs] at this
    rw [hz, hy] at this
    exact add_right_cancel this
  simp only [Prod.mk.injEq]
  exact ⟨hz, hx, hy⟩

/-! ### Reduction to textbook single-generator discrete log -/

/-- The reduction built from `A` wins the textbook single-generator DL game with probability at
most `bound`. Its winning coins are those on which `discreteLogOfChallenge_of_relation`, applied
to `programmedEmbedding`, computes the discrete log of `z • B`.

Only a nonzero `B` makes this a hardness claim. At `B = 0` the presented basis is constant and
carries no challenge, so a fixed nonzero relation wins on all but a `1/|F|` fraction of coins and
no `bound` below `1 - 1/|F|` holds. The degenerate case is not unsound — the bounds below stay
true and go trivial — and `B ≠ 0` is demanded where it is load-bearing, at
`Zcash.Snark.orchard_uniformURSIdentification_of_generatorRO`. -/
def TextbookDLAdvantageLE (bound : ℝ≥0∞) : Prop :=
  (PMF.uniformOfFintype (F × (ι → F) × (ι → F))).toOuterMeasure (winSet B A) ≤ bound

/-- Under textbook DL hardness, relation finding has probability at most `bound + 1/|F|` — the
tight Jaeger–Tessaro form, with no multiplicative loss. -/
theorem relation_prob_le_of_textbookDL {bound : ℝ≥0∞} (h : TextbookDLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A)
      ≤ bound + 1 / Fintype.card F := by
  haveI : Nonempty (ι → F) := ⟨fun _ => 0⟩
  have hM0 : (Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hMtop : (Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hC0 : (Fintype.card (F × (ι → F)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hCtop : (Fintype.card (F × (ι → F)) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hwin : ((winSet B A).card : ℝ≥0∞) / Fintype.card (F × (ι → F) × (ι → F)) ≤ bound := by
    rw [← uniformOfFintype_toOuterMeasure_finset]
    exact h
  have hmiss : ((missSet B A).card : ℝ≥0∞) / Fintype.card (F × (ι → F) × (ι → F))
      ≤ 1 / Fintype.card F := by
    have hcard : ((missSet B A).card : ℝ≥0∞) ≤ Fintype.card ((ι → F) × (ι → F)) := by
      exact_mod_cast missSet_card_le B A
    have hN : (Fintype.card (F × (ι → F) × (ι → F)) : ℝ≥0∞)
        = (Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞) * Fintype.card F := by
      push_cast [Fintype.card_prod]
      ring
    calc ((missSet B A).card : ℝ≥0∞) / Fintype.card (F × (ι → F) × (ι → F))
        ≤ (Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞)
            / Fintype.card (F × (ι → F) × (ι → F)) := by gcongr
      _ = 1 / Fintype.card F := by
          rw [hN]
          calc (Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞)
                / ((Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞) * Fintype.card F)
              = (Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞) * 1
                  / ((Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞) * Fintype.card F) := by
                rw [mul_one]
            _ = 1 / Fintype.card F := ENNReal.mul_div_mul_left _ _ hM0 hMtop
  have hrel : (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A)
      = ((programmedRelSet B A).card : ℝ≥0∞)
          / Fintype.card (F × (ι → F) × (ι → F)) := by
    rw [uniformOfFintype_toOuterMeasure_finset, programmedRelSet_card]
    have hN : (Fintype.card (F × (ι → F) × (ι → F)) : ℝ≥0∞)
        = (Fintype.card (F × (ι → F)) : ℝ≥0∞) * Fintype.card (ι → F) := by
      push_cast [Fintype.card_prod]
      ring
    rw [hN]
    push_cast
    rw [mul_comm ((relSet B A).card : ℝ≥0∞) (Fintype.card (F × (ι → F)) : ℝ≥0∞),
      ENNReal.mul_div_mul_left _ _ hC0 hCtop]
  have hsplit : ((programmedRelSet B A).card : ℝ≥0∞)
      ≤ ((winSet B A).card : ℝ≥0∞) + ((missSet B A).card : ℝ≥0∞) := by
    exact_mod_cast le_trans
      (Finset.card_le_card (programmedRelSet_subset_win_union_miss B A))
      (Finset.card_union_le _ _)
  calc (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A)
      = ((programmedRelSet B A).card : ℝ≥0∞)
          / Fintype.card (F × (ι → F) × (ι → F)) := hrel
    _ ≤ (((winSet B A).card : ℝ≥0∞) + ((missSet B A).card : ℝ≥0∞))
          / Fintype.card (F × (ι → F) × (ι → F)) := by gcongr
    _ = ((winSet B A).card : ℝ≥0∞) / Fintype.card (F × (ι → F) × (ι → F))
          + ((missSet B A).card : ℝ≥0∞) / Fintype.card (F × (ι → F) × (ι → F)) := by
        rw [← ENNReal.div_add_div_same]
    _ ≤ bound + 1 / Fintype.card F := add_le_add hwin hmiss

end Reduction

end Zcash
