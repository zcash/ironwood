import Zcash.Circuits.Integration.PermutationColumns
import Zcash.Circuits.Halo2.CopyCells
import Zcash.Common.RelationWitness
import Zcash.Snark.Keygen.Lagrange

/-!
# The executable keygen assembly replay is the abstract permutation replay

`Layout.runAssembly` replays halo2's `Assembly::copy` over the derived copy list with
arrays and union-find bookkeeping; the permutation semantics
(`ResolverPermutationCycle.ofKeygenColumns`, `keygenSigmaColumn`) speak about the
abstract swap-composition replay `replayKeygenPermutation`. This module proves they are
the same permutation: the assembly's `mapping` is the abstract permutation's action, and
its `aux` classes are exactly the cycles.

The simulation invariant `Asm.Sim` carries three facts through the copy fold: `mapping`
acts as the permutation, every `aux` entry is an in-cycle representative, and `aux`
entries agree exactly on cycles. The union-find size heuristic needs no invariant — it
only selects which representative survives a merge, and the cycle partition is
representative-agnostic.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (deltaFp omegaOf)

open Halo2 Halo2.Layout
open Equiv (Perm swap)

set_option maxHeartbeats 400000

namespace Layout.Asm

open Halo2.Layout.Asm

/-- The rectangular shape invariant of the assembly's cell arrays. -/
def Shaped (numCols n : ℕ) (a : Array (Array (ℕ × ℕ))) : Prop :=
  a.size = numCols ∧ ∀ i, (h : i < a.size) → a[i].size = n

/-- Simulation between an assembly state and an abstract cell permutation: the shape of
both cell arrays, `mapping` acting as the permutation, every `aux` entry an in-cycle,
self-rooted representative, and `aux` entries agreeing exactly on cycles. -/
structure Sim {numCols n : ℕ} (a : Asm) (π : Perm (FlatCell numCols n)) : Prop where
  map_shape : Shaped numCols n a.mapping
  aux_shape : Shaped numCols n a.aux
  map_eq : ∀ c : FlatCell numCols n,
    getPair a.mapping c.pair = (π c).pair
  aux_rep : ∀ c : FlatCell numCols n, ∃ r : FlatCell numCols n,
    getPair a.aux c.pair = r.pair ∧ π.SameCycle c r ∧
      getPair a.aux r.pair = r.pair
  aux_eq_iff : ∀ c d : FlatCell numCols n,
    (getPair a.aux c.pair = getPair a.aux d.pair ↔ π.SameCycle c d)

/-- `repoint` never touches `mapping`. -/
theorem repoint_mapping (a : Asm) (fuel : ℕ) (i tgt stop : ℕ × ℕ) :
    (repoint a fuel i tgt stop).mapping = a.mapping := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [repoint]
      split
      · rfl
      · exact ih _ _

/-- `repoint` never touches `sizes`. -/
theorem repoint_sizes (a : Asm) (fuel : ℕ) (i tgt stop : ℕ × ℕ) :
    (repoint a fuel i tgt stop).sizes = a.sizes := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [repoint]
      split
      · rfl
      · exact ih _ _

theorem Shaped.setPair {numCols n : ℕ} {a : Array (Array (ℕ × ℕ))}
    (h : Shaped numCols n a) (p : ℕ × ℕ) (v : ℕ × ℕ) :
    Shaped numCols n (setPair a p v) := by
  obtain ⟨hsize, hrow⟩ := h
  refine ⟨by simpa [Halo2.Layout.Asm.setPair] using hsize, ?_⟩
  intro i hi
  simp only [Halo2.Layout.Asm.setPair, Array.size_modify] at hi
  by_cases hip : p.1 = i
  · subst hip
    simp [Halo2.Layout.Asm.setPair, Array.getElem_modify_self, hrow]
  · simp [Halo2.Layout.Asm.setPair, Array.getElem_modify_of_ne hip, hrow]

/-- Reading back the just-written cell (the write position must be in shape). -/
theorem getPair_setPair_self {numCols n : ℕ} {a : Array (Array (ℕ × ℕ))}
    (h : Shaped numCols n a) {p : ℕ × ℕ} (hp1 : p.1 < numCols) (hp2 : p.2 < n)
    (v : ℕ × ℕ) :
    getPair (setPair a p v) p = v := by
  obtain ⟨hsize, hrow⟩ := h
  have hp1' : p.1 < a.size := hsize ▸ hp1
  simp [Halo2.Layout.Asm.getPair, Halo2.Layout.Asm.setPair,
    Array.size_modify, hp1', Array.getElem_modify_self,
    Array.set!, Array.getElem_setIfInBounds_self, hrow _ hp1', hp2]

/-- Reading any other cell is unaffected by the write. -/
theorem getPair_setPair_ne {numCols n : ℕ} {a : Array (Array (ℕ × ℕ))}
    (h : Shaped numCols n a) {p q : ℕ × ℕ} (hpq : q ≠ p) (v : ℕ × ℕ) :
    getPair (setPair a p v) q = getPair a q := by
  obtain ⟨hsize, hrow⟩ := h
  by_cases h1 : q.1 = p.1
  · have h2 : q.2 ≠ p.2 := fun h2 => hpq (Prod.ext_iff.mpr ⟨h1, h2⟩)
    by_cases hq1 : q.1 < a.size
    · have hp1 : p.1 < a.size := h1 ▸ hq1
      simp [Halo2.Layout.Asm.getPair, Halo2.Layout.Asm.setPair, Array.getElem!_eq_getD, Array.getD,
        Array.size_modify, h1, Array.getElem_modify_self,
        Array.set!, Array.size_setIfInBounds, hp1]
      split
      · exact Array.getElem_setIfInBounds_ne (by assumption) (Ne.symm h2)
      · rfl
    · simp [Halo2.Layout.Asm.getPair, Halo2.Layout.Asm.setPair, Array.getElem!_eq_getD, Array.getD,
        Array.size_modify, hq1]
  · simp [Halo2.Layout.Asm.getPair, Halo2.Layout.Asm.setPair, Array.getElem!_eq_getD, Array.getD,
      Array.size_modify, Array.getElem_modify_of_ne (fun h => h1 h.symm)]

/-- `repoint` preserves the aux shape. -/
theorem Shaped.repoint {numCols n : ℕ} {a : Asm}
    (h : Shaped numCols n a.aux) (fuel : ℕ) (i tgt stop : ℕ × ℕ) :
    Shaped numCols n (Halo2.Layout.Asm.repoint a fuel i tgt stop).aux := by
  induction fuel generalizing a i with
  | zero => exact h
  | succ fuel ih =>
      simp only [Halo2.Layout.Asm.repoint]
      split
      · exact h.setPair i tgt
      · exact ih (h.setPair i tgt) _

/-- The effect of one `repoint` walk: with `mapping` acting as `π`, the walk from
`start` (with stop `stop`, the first later return of the orbit) re-points exactly the
orbit segment `π ^ t · start, t < s`, and leaves every other `aux` entry unchanged. -/
theorem getPair_repoint_aux {numCols n : ℕ} {a : Asm} {π : Perm (FlatCell numCols n)}
    (hshape : Shaped numCols n a.aux)
    (hmap : ∀ c : FlatCell numCols n, getPair a.mapping c.pair = (π c).pair)
    (s : ℕ) (start stop : FlatCell numCols n) (tgt : ℕ × ℕ)
    (hs : (π ^ s) start = stop) (hs1 : 1 ≤ s)
    (hmin : ∀ t, 0 < t → t < s → (π ^ t) start ≠ stop)
    (fuel : ℕ) (hfuel : s ≤ fuel)
    (d : FlatCell numCols n) :
    getPair (Halo2.Layout.Asm.repoint a fuel start.pair tgt stop.pair).aux d.pair =
      if ∃ t, t < s ∧ (π ^ t) start = d then tgt else getPair a.aux d.pair := by
  induction s generalizing a start fuel with
  | zero => exact absurd hs1 (by omega)
  | succ s' ih =>
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
        ⟨fuel - 1, by omega⟩
      have hnext : getPair a.mapping start.pair = (π start).pair := hmap start
      by_cases hzero : s' = 0
      · -- one step: the walk immediately returns to `stop`
        subst hzero
        have hstop : π start = stop := by
          simpa [pow_one] using hs
        simp only [Halo2.Layout.Asm.repoint, hnext, hstop]
        rw [if_pos (by simp)]
        by_cases hd : d = start
        · subst hd
          rw [if_pos ⟨0, by simp, rfl⟩]
          exact getPair_setPair_self hshape d.1.isLt d.2.isLt tgt
        · rw [if_neg ?_, getPair_setPair_ne hshape ?_ tgt]
          · exact fun h => hd (FlatCell.pair_injective h)
          · rintro ⟨t, ht, hteq⟩
            interval_cases t
            exact hd (by simpa using hteq.symm)
      · -- the walk continues: `π start ≠ stop`, recurse along the orbit
        have hs'1 : 1 ≤ s' := by omega
        have hne : π start ≠ stop := by
          simpa [pow_one] using hmin 1 (by omega) (by omega)
        have hnepair : ((π start).pair == stop.pair) = false := by
          simp only [beq_eq_false_iff_ne]
          exact fun h => hne (FlatCell.pair_injective h)
        simp only [Halo2.Layout.Asm.repoint, hnext, hnepair]
        rw [if_neg (by simp)]
        have hs'' : (π ^ s') (π start) = stop := by
          rw [← Equiv.Perm.mul_apply, ← pow_succ]
          exact hs
        have hmin'' : ∀ t, 0 < t → t < s' → (π ^ t) (π start) ≠ stop := by
          intro t ht hts habs
          refine hmin (t + 1) (by omega) (by omega) ?_
          rw [pow_succ, Equiv.Perm.mul_apply]
          exact habs
        have hrec := ih (a := { a with aux := setPair a.aux start.pair tgt })
          (hshape.setPair start.pair tgt) hmap (π start) hs'' hs'1 hmin'' f (by omega) 
        rw [hrec]
        by_cases hd : d = start
        · subst hd
          have hrhs : ∃ t, t < s' + 1 ∧ (π ^ t) d = d := ⟨0, by simp⟩
          rw [if_pos hrhs]
          split
          · rfl
          · exact getPair_setPair_self hshape d.1.isLt d.2.isLt tgt
        · have hpairne : d.pair ≠ start.pair :=
            fun h => hd (FlatCell.pair_injective h)
          have hcond : (∃ t, t < s' ∧ (π ^ t) (π start) = d) ↔
              (∃ t, t < s' + 1 ∧ (π ^ t) start = d) := by
            constructor
            · rintro ⟨t, ht, hteq⟩
              refine ⟨t + 1, by omega, ?_⟩
              rw [pow_succ, Equiv.Perm.mul_apply]
              exact hteq
            · rintro ⟨t, ht, hteq⟩
              match t with
              | 0 => exact absurd (by simpa using hteq.symm) hd
              | t + 1 =>
                  refine ⟨t, by omega, ?_⟩
                  rw [pow_succ, Equiv.Perm.mul_apply] at hteq
                  exact hteq
          rw [getPair_setPair_ne hshape hpairne tgt]
          by_cases hc : ∃ t, t < s' + 1 ∧ (π ^ t) start = d
          · rw [if_pos hc, if_pos (hcond.mpr hc)]
          · rw [if_neg hc, if_neg (fun h => hc (hcond.mp h))]

/-- Every cell has a first return time under a permutation of the flat cells, bounded by
the cell count. -/
theorem exists_minimal_return {numCols n : ℕ} (π : Perm (FlatCell numCols n))
    (rep : FlatCell numCols n) :
    ∃ s, (1 ≤ s ∧ (π ^ s) rep = rep) ∧ s ≤ numCols * n ∧
      ∀ t, 0 < t → t < s → (π ^ t) rep ≠ rep := by
  classical
  have hex : ∃ t, 1 ≤ t ∧ (π ^ t) rep = rep := by
    refine ⟨orderOf π, orderOf_pos π, ?_⟩
    rw [pow_orderOf_eq_one]
    rfl
  let s := Nat.find hex
  have hfind := Nat.find_spec hex
  have hmin : ∀ t, 0 < t → t < s → (π ^ t) rep ≠ rep := by
    intro t ht hts habs
    exact Nat.find_min hex hts ⟨ht, habs⟩
  refine ⟨s, hfind, ?_, hmin⟩
  -- `t ↦ π ^ t rep` is injective below the first return, so `s` is at most the cell count
  have hinj : Set.InjOn (fun t => (π ^ t) rep) (Finset.range s) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    by_contra hne
    -- w.l.o.g. x < y; then `π ^ (y - x) rep = rep` strictly before `s`
    rcases Nat.lt_or_ge x y with hlt | hge
    · have : (π ^ (y - x)) rep = rep := by
        apply (Equiv.injective (π ^ x))
        rw [← Equiv.Perm.mul_apply, ← pow_add]
        rw [Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
        exact hxy.symm
      exact hmin (y - x) (by omega) (by omega) this
    · have hlt' : y < x := by omega
      have : (π ^ (x - y)) rep = rep := by
        apply (Equiv.injective (π ^ y))
        rw [← Equiv.Perm.mul_apply, ← pow_add]
        rw [Nat.add_sub_cancel' (Nat.le_of_lt hlt')]
        exact hxy
      exact hmin (x - y) (by omega) (by omega) this
  have hcard := Finset.card_le_card_of_injOn (fun t => (π ^ t) rep)
    (fun x _ => Finset.mem_univ _) hinj
  simpa [Fintype.card_prod] using hcard

/-- Below the first return time, the orbit segment of a cell is exactly its cycle. -/
theorem sameCycle_iff_exists_pow_lt {numCols n : ℕ} {π : Perm (FlatCell numCols n)}
    {rep : FlatCell numCols n} {s : ℕ} (hs1 : 1 ≤ s) (hs : (π ^ s) rep = rep)
    (d : FlatCell numCols n) :
    π.SameCycle rep d ↔ ∃ t, t < s ∧ (π ^ t) rep = d := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
    have hq : ∀ q, (π ^ (s * q)) rep = rep := by
      intro q
      induction q with
      | zero => rfl
      | succ q ih =>
          rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, hs]
          exact ih
    refine ⟨i % s, Nat.mod_lt _ (by omega), ?_⟩
    conv_rhs => rw [← hi, ← Nat.mod_add_div i s]
    rw [pow_add, Equiv.Perm.mul_apply, hq]
  · rintro ⟨t, _, rfl⟩
    exact ⟨(t : ℤ), by simp⟩

/-- The walk reads only `mapping` and writes only `aux`, so a `sizes` update commutes
away. -/
theorem repoint_aux_sizes {a : Asm} (sz : Array (Array ℕ)) (fuel : ℕ)
    (i tgt stop : ℕ × ℕ) :
    (Halo2.Layout.Asm.repoint { a with sizes := sz }
        fuel i tgt stop).aux =
      (Halo2.Layout.Asm.repoint a fuel i tgt stop).aux := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [Halo2.Layout.Asm.repoint]
      split
      · rfl
      · exact ih (a := { a with aux := setPair a.aux i tgt }) _

/-- The mapping component of a merge: the two-entry swap over the untouched mapping. -/
theorem merge_mapping (a : Asm) (fuel : ℕ) (lp rp : ℕ × ℕ) :
    (Halo2.Layout.Asm.merge a fuel lp rp).mapping =
      setPair (setPair a.mapping lp (getPair a.mapping rp)) rp
        (getPair a.mapping lp) := by
  simp only [Halo2.Layout.Asm.merge, repoint_mapping]

/-- The aux component of a merge: the re-pointing walk over the untouched aux, from and
to the absorbed representative, targeting the surviving one. -/
theorem merge_aux (a : Asm) (fuel : ℕ) (lp rp : ℕ × ℕ) :
    (Halo2.Layout.Asm.merge a fuel lp rp).aux =
      (Halo2.Layout.Asm.repoint a fuel
        (if getNat a.sizes (getPair a.aux lp) < getNat a.sizes (getPair a.aux rp)
          then getPair a.aux lp else getPair a.aux rp)
        (if getNat a.sizes (getPair a.aux lp) < getNat a.sizes (getPair a.aux rp)
          then getPair a.aux rp else getPair a.aux lp)
        (if getNat a.sizes (getPair a.aux lp) < getNat a.sizes (getPair a.aux rp)
          then getPair a.aux lp else getPair a.aux rp)).aux := by
  simp only [Halo2.Layout.Asm.merge, repoint_aux_sizes]

open Halo2.Layout.Asm in
/-- One assembly `copy` simulates one abstract merge step, with walk fuel covering any
cycle length. -/
theorem Sim.copy {numCols n : ℕ} {a : Asm} {π : Perm (FlatCell numCols n)}
    (sim : Sim a π) (l r : FlatCell numCols n) :
    Sim (Halo2.Layout.Asm.copy a (n * numCols)
        l.pair.1 l.pair.2 r.pair.1 r.pair.2)
      (PermConstruction.step π (l, r)) := by
  classical
  obtain ⟨L, hL, hLcyc, hLroot⟩ := sim.aux_rep l
  obtain ⟨R, hR, hRcyc, hRroot⟩ := sim.aux_rep r
  have hpl : ((l.pair.1, l.pair.2) : ℕ × ℕ) = l.pair := rfl
  have hpr : ((r.pair.1, r.pair.2) : ℕ × ℕ) = r.pair := rfl
  rw [Halo2.Layout.Asm.copy, PermConstruction.step]
  by_cases hsame : π.SameCycle l r
  · have heq : getPair a.aux l.pair = getPair a.aux r.pair :=
      (sim.aux_eq_iff l r).mpr hsame
    rw [if_pos hsame, if_pos (by simpa [hpl, hpr] using heq)]
    exact sim
  · have hbeq : ¬ (getPair a.aux (l.pair.1, l.pair.2) ==
        getPair a.aux (r.pair.1, r.pair.2)) = true := by
      simp only [hpl, hpr, beq_iff_eq]
      exact fun h => hsame ((sim.aux_eq_iff l r).mp h)
    rw [if_neg hsame, if_neg hbeq]
    -- representative cells and their source cells, by the size comparison
    set RC : FlatCell numCols n :=
      if getNat a.sizes (getPair a.aux (l.pair.1, l.pair.2)) <
          getNat a.sizes (getPair a.aux (r.pair.1, r.pair.2)) then L else R with hRC
    set LC : FlatCell numCols n :=
      if getNat a.sizes (getPair a.aux (l.pair.1, l.pair.2)) <
          getNat a.sizes (getPair a.aux (r.pair.1, r.pair.2)) then R else L with hLC
    set u : FlatCell numCols n :=
      if getNat a.sizes (getPair a.aux (l.pair.1, l.pair.2)) <
          getNat a.sizes (getPair a.aux (r.pair.1, r.pair.2)) then l else r with hu
    set v : FlatCell numCols n :=
      if getNat a.sizes (getPair a.aux (l.pair.1, l.pair.2)) <
          getNat a.sizes (getPair a.aux (r.pair.1, r.pair.2)) then r else l with hv
    have hRCpair : (if getNat a.sizes (getPair a.aux (l.pair.1, l.pair.2)) <
        getNat a.sizes (getPair a.aux (r.pair.1, r.pair.2))
        then getPair a.aux (l.pair.1, l.pair.2)
        else getPair a.aux (r.pair.1, r.pair.2)) = RC.pair := by
      rw [hRC]; split <;> simp [hpl, hpr, hL, hR]
    have hLCpair : (if getNat a.sizes (getPair a.aux (l.pair.1, l.pair.2)) <
        getNat a.sizes (getPair a.aux (r.pair.1, r.pair.2))
        then getPair a.aux (r.pair.1, r.pair.2)
        else getPair a.aux (l.pair.1, l.pair.2)) = LC.pair := by
      rw [hLC]; split <;> simp [hpl, hpr, hL, hR]
    have hRCcyc : π.SameCycle u RC := by
      rw [hRC, hu]; split <;> assumption
    have hLCcyc : π.SameCycle v LC := by
      rw [hLC, hv]; split <;> assumption
    have hLCroot : getPair a.aux LC.pair = LC.pair := by
      rw [hLC]; split <;> assumption
    have hvrep : getPair a.aux v.pair = LC.pair := by
      rw [hv, hLC]; split <;> assumption
    have huv : ¬ π.SameCycle u v := by
      rw [hu, hv]
      split
      · exact hsame
      · exact fun h => hsame h.symm
    have hRCLC : ¬ π.SameCycle RC LC :=
      fun h => huv (hRCcyc.trans (h.trans hLCcyc.symm))
    obtain ⟨sN, ⟨hs1, hsret⟩, hsle, hsmin⟩ := exists_minimal_return π RC
    -- the aux component after the merge, cycle by cycle
    have haux2 : ∀ d : FlatCell numCols n,
        getPair (Halo2.Layout.Asm.merge a (n * numCols)
            (l.pair.1, l.pair.2) (r.pair.1, r.pair.2)).aux d.pair =
          if π.SameCycle RC d then LC.pair else getPair a.aux d.pair := by
      intro d
      rw [merge_aux, hRCpair, hLCpair]
      rw [getPair_repoint_aux sim.aux_shape sim.map_eq sN RC RC LC.pair
        hsret hs1 hsmin (n * numCols)
        (le_trans hsle (le_of_eq (Nat.mul_comm _ _))) d]
      by_cases hcyc : π.SameCycle RC d
      · rw [if_pos ((sameCycle_iff_exists_pow_lt hs1 hsret d).mp hcyc), if_pos hcyc]
      · rw [if_neg (fun h => hcyc ((sameCycle_iff_exists_pow_lt hs1 hsret d).mpr h)),
          if_neg hcyc]
    have hlr : l ≠ r := fun h => hsame (h ▸ Equiv.Perm.SameCycle.refl π l)
    have hlrpair : l.pair ≠ r.pair := fun h => hlr (FlatCell.pair_injective h)
    have hmerge : ∀ c d : FlatCell numCols n,
        (π * Equiv.swap l r).SameCycle c d ↔ PermConstruction.MergeRel π l r c d :=
      PermConstruction.sameCycle_mul_swap hsame
    have huvlr : (u = l ∧ v = r) ∨ (u = r ∧ v = l) := by
      rw [hu, hv]
      split
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    -- membership in the absorbed cycle relates through the merge to the surviving one
    have hMergeOfRC : ∀ {e : FlatCell numCols n}, π.SameCycle RC e →
        ∀ {f : FlatCell numCols n}, π.SameCycle v f →
        PermConstruction.MergeRel π l r e f := by
      intro e he f hf
      have heu : π.SameCycle e u := he.symm.trans hRCcyc.symm
      have hfv : π.SameCycle f v := hf.symm
      rcases huvlr with ⟨hul, hvr⟩ | ⟨hur, hvl⟩
      · exact Or.inr (Or.inl ⟨hul ▸ heu, hvr ▸ hfv⟩)
      · exact Or.inr (Or.inr ⟨hur ▸ heu, hvl ▸ hfv⟩)
    have hMergeElim : ∀ {e f : FlatCell numCols n},
        PermConstruction.MergeRel π l r e f → π.SameCycle RC e →
        ¬ π.SameCycle RC f → π.SameCycle v f := by
      intro e f hm he hf
      rcases hm with hm | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (he.trans hm) hf
      · -- e ~ l, f ~ r
        rcases huvlr with ⟨hul, hvr⟩ | ⟨hur, hvl⟩
        · exact hvr ▸ h2.symm
        · exact absurd ((((hur ▸ hRCcyc : π.SameCycle r RC).trans he).trans h1).symm)
            hsame
      · -- e ~ r, f ~ l
        rcases huvlr with ⟨hul, hvr⟩ | ⟨hur, hvl⟩
        · exact absurd (((hul ▸ hRCcyc : π.SameCycle l RC).trans he).trans h1) hsame
        · exact hvl ▸ h2.symm
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- mapping shape: two writes over the untouched mapping
      rw [merge_mapping]
      exact (sim.map_shape.setPair _ _).setPair _ _
    · -- aux shape: one walk over the untouched aux
      rw [merge_aux]
      exact Shaped.repoint sim.aux_shape _ _ _ _
    · -- the mapping acts as the merged permutation
      intro c
      rw [merge_mapping, hpl, hpr]
      have hswap : (π * Equiv.swap l r) c = π (Equiv.swap l r c) :=
        Equiv.Perm.mul_apply _ _ _
      by_cases hcr : c = r
      · subst hcr
        rw [getPair_setPair_self (sim.map_shape.setPair _ _) c.1.isLt c.2.isLt,
          sim.map_eq l, hswap, Equiv.swap_apply_right]
      · have hcrpair : c.pair ≠ r.pair := fun h => hcr (FlatCell.pair_injective h)
        rw [getPair_setPair_ne (sim.map_shape.setPair _ _) hcrpair]
        by_cases hcl : c = l
        · subst hcl
          rw [getPair_setPair_self sim.map_shape c.1.isLt c.2.isLt,
            sim.map_eq r, hswap, Equiv.swap_apply_left]
        · have hclpair : c.pair ≠ l.pair := fun h => hcl (FlatCell.pair_injective h)
          rw [getPair_setPair_ne sim.map_shape hclpair, sim.map_eq c, hswap,
            Equiv.swap_apply_of_ne_of_ne hcl hcr]
    · -- every cell keeps an in-cycle, self-rooted representative
      intro c
      by_cases hc : π.SameCycle RC c
      · refine ⟨LC, by rw [haux2 c, if_pos hc], ?_, ?_⟩
        · exact (hmerge c LC).mpr (hMergeOfRC hc hLCcyc)
        · rw [haux2 LC, if_neg hRCLC]
          exact hLCroot
      · obtain ⟨rep, hrep, hrepcyc, hreproot⟩ := sim.aux_rep c
        refine ⟨rep, by rw [haux2 c, if_neg hc]; exact hrep,
          (hmerge c rep).mpr (Or.inl hrepcyc), ?_⟩
        have hrc : ¬ π.SameCycle RC rep := fun h => hc (h.trans hrepcyc.symm)
        rw [haux2 rep, if_neg hrc]
        exact hreproot
    · -- aux entries agree exactly on merged cycles
      intro c d
      rw [haux2 c, haux2 d, hmerge c d]
      by_cases hc : π.SameCycle RC c <;> by_cases hd : π.SameCycle RC d
      · rw [if_pos hc, if_pos hd]
        exact ⟨fun _ => Or.inl (hc.symm.trans hd), fun _ => rfl⟩
      · rw [if_pos hc, if_neg hd]
        constructor
        · intro h
          have hdv : π.SameCycle d v :=
            (sim.aux_eq_iff d v).mp (by rw [hvrep, ← h])
          exact hMergeOfRC hc hdv.symm
        · intro hm
          have hdv : π.SameCycle v d := hMergeElim hm hc hd
          have : getPair a.aux d.pair = getPair a.aux v.pair :=
            (sim.aux_eq_iff d v).mpr hdv.symm
          rw [this, hvrep]
      · rw [if_neg hc, if_pos hd]
        constructor
        · intro h
          have hcv : π.SameCycle c v :=
            (sim.aux_eq_iff c v).mp (by rw [hvrep, h])
          exact PermConstruction.mergeRel_symm (hMergeOfRC hd hcv.symm)
        · intro hm
          have hcv : π.SameCycle v c :=
            hMergeElim (PermConstruction.mergeRel_symm hm) hd hc
          have : getPair a.aux c.pair = getPair a.aux v.pair :=
            (sim.aux_eq_iff c v).mpr hcv.symm
          rw [this, hvrep]
      · rw [if_neg hc, if_neg hd, sim.aux_eq_iff c d]
        constructor
        · exact fun h => Or.inl h
        · intro hm
          rcases hm with hm | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hm
          · rcases huvlr with ⟨hul, hvr⟩ | ⟨hur, hvl⟩
            · exact absurd (h1.trans (hul ▸ hRCcyc)).symm hc
            · exact absurd (h2.trans (hur ▸ hRCcyc)).symm hd
          · rcases huvlr with ⟨hul, hvr⟩ | ⟨hur, hvl⟩
            · exact absurd (h2.trans (hul ▸ hRCcyc)).symm hd
            · exact absurd (h1.trans (hur ▸ hRCcyc)).symm hc

/-- The fresh assembly simulates the identity permutation. -/
theorem Sim.new (numCols n : ℕ) :
    Sim (numCols := numCols) (n := n)
      (Halo2.Layout.Asm.new n numCols) 1 := by
  have hget : ∀ c : FlatCell numCols n,
      getPair ((Array.range numCols).map
        (fun i => Halo2.Layout.Asm.initCol i n)) c.pair = c.pair := by
    intro c
    simp [Halo2.Layout.Asm.getPair,
      Halo2.Layout.Asm.initCol,
      FlatCell.pair, c.1.isLt, c.2.isLt]
  have hshape : Shaped numCols n ((Array.range numCols).map
      (fun i => Halo2.Layout.Asm.initCol i n)) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    simp only [Array.size_map, Array.size_range] at hi
    simp [Halo2.Layout.Asm.initCol]
  have hgetm : ∀ c : FlatCell numCols n,
      getPair (Halo2.Layout.Asm.new n numCols).mapping c.pair =
        c.pair := fun c => hget c
  have hgeta : ∀ c : FlatCell numCols n,
      getPair (Halo2.Layout.Asm.new n numCols).aux c.pair =
        c.pair := fun c => hget c
  refine ⟨hshape, hshape, ?_, ?_, ?_⟩
  · intro c
    simpa using hgetm c
  · intro c
    exact ⟨c, hgeta c, Equiv.Perm.SameCycle.refl 1 c, hgeta c⟩
  · intro c d
    rw [hgeta c, hgeta d]
    constructor
    · intro h
      rw [Equiv.Perm.sameCycle_one]
      exact FlatCell.pair_injective h
    · intro h
      rw [Equiv.Perm.sameCycle_one] at h
      rw [h]

/-- The simulation survives a whole copy fold. -/
theorem Sim.foldl {numCols n : ℕ}
    (copies : List (FlatCell numCols n × FlatCell numCols n))
    {a : Asm} {π : Perm (FlatCell numCols n)} (sim : Sim a π) :
    Sim (copies.foldl (fun st p =>
        Halo2.Layout.Asm.copy st (n * numCols)
          p.1.pair.1 p.1.pair.2 p.2.pair.1 p.2.pair.2) a)
      (copies.foldl PermConstruction.step π) := by
  induction copies generalizing a π with
  | nil => exact sim
  | cons p rest ih => exact ih (sim.copy p.1 p.2)

/-- The abstract replay is the copy-order fold of the merge step. -/
theorem replayKeygenPermutation_eq_foldl {cell : Type*} [DecidableEq cell] [Fintype cell]
    (copies : List (cell × cell)) :
    replayKeygenPermutation copies = copies.foldl PermConstruction.step 1 := by
  have hbuild : ∀ l : List (cell × cell),
      PermConstruction.build l = l.foldr (fun ab π => PermConstruction.step π ab) 1 := by
    intro l
    induction l with
    | nil => rfl
    | cons ab rest ih => simp [PermConstruction.build, ih]
  rw [replayKeygenPermutation, hbuild, List.foldr_reverse]

/-- **The executable keygen assembly is the abstract replay**: on every cell, the final
`mapping` is the action of `replayKeygenPermutation` over the same copies. -/
theorem runAssembly_getPair {numCols n : ℕ}
    (copies : List (FlatCell numCols n × FlatCell numCols n))
    (c : FlatCell numCols n) :
    getPair (Halo2.Layout.runAssembly n numCols
        (copies.map fun p => (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2))) c.pair =
      ((replayKeygenPermutation copies) c).pair := by
  rw [Halo2.Layout.runAssembly]
  rw [List.foldl_map]
  rw [replayKeygenPermutation_eq_foldl]
  exact (Sim.foldl copies (Sim.new numCols n)).map_eq c

/-- A generated σ-table entry is the δ/ω name of the replayed permutation's image cell:
the executable pipeline reads the assembly mapping at `(column, row)`, and the mapping's
action is the abstract replay. -/
theorem permPolysOf_getD_eq {k : ℕ} (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (copies' : List (FlatCell (Halo2.Layout.permColsOf cs).length (2 ^ k) ×
      FlatCell (Halo2.Layout.permColsOf cs).length (2 ^ k)))
    (hcopies : Halo2.Layout.V1.copyList (Halo2.Layout.permColsOf cs)
        (Halo2.FloorPlanner.V1.starts ops) ops
        (Halo2.Layout.constantCopyEntries cs ops) =
      copies'.map fun p => (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2))
    (g : Fin (Halo2.Layout.permColsOf cs).length) (j : Fin (2 ^ k)) :
    ((Keygen.permPolysOf k cs ops).getD (g : ℕ) []).getD (j : ℕ) 0 =
      deltaFp ^ ((replayKeygenPermutation copies' (g, j)).1 : ℕ) *
        omegaOf k ^ ((replayKeygenPermutation copies' (g, j)).2 : ℕ) := by
  have hmap' : ((Halo2.Layout.runAssembly (2 ^ k)
      (Halo2.Layout.permColsOf cs).length (copies'.map fun p =>
        (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2)))[(g : ℕ)]!)[(j : ℕ)]! =
      (replayKeygenPermutation copies' (g, j)).pair :=
    Layout.Asm.runAssembly_getPair copies' (g, j)
  simp only [Keygen.permPolysOf]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range g.isLt, List.getElem?_range j.isLt,
    Option.map_some, Option.getD_some]
  rw [hcopies, hmap']
  simp only [FlatCell.pair]
  rw [Keygen.deltaPowersArr_getElem! _
      (replayKeygenPermutation copies' (g, j)).1.isLt,
    Keygen.omegaPowersArr_getElem! _
      (replayKeygenPermutation copies' (g, j)).2.isLt]

/-- **The σ-row name fact (`hval`), generically.** Reading the derived σ table at a
cell's global column and row gives the identity name of the cell's image under the
chunk-shaped replay — the exact premise of the σ-column identification. The chunk
layout enters through `flatten` (cells against `(row, global column)` pairs) and its
compatibility facts: the flattening preserves rows, and a cell's chunk/column recompose
to its global column. -/
theorem permPolysOf_getD_eq_chunkRowName {k : ℕ}
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    {numCols n : ℕ} (hcount : numCols = (Halo2.Layout.permColsOf cs).length)
    (hsize : n = 2 ^ k)
    (copies' : List (FlatCell numCols n ×
      FlatCell numCols n))
    (hcopies : Halo2.Layout.V1.copyList (Halo2.Layout.permColsOf cs)
        (Halo2.FloorPlanner.V1.starts ops) ops
        (Halo2.Layout.constantCopyEntries cs ops) =
      copies'.map fun p => (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2))
    {nc : ℕ} {width : ℕ → ℕ} (chunkLen : ℕ)
    (flatten : ChunkCell nc n width ≃
      Fin n × Fin numCols)
    (hrow : ∀ rc : Fin n × Fin numCols,
      ((flatten.symm rc).2.1 : ℕ) = (rc.1 : ℕ))
    (hcol : ∀ rc : Fin n × Fin numCols,
      ((flatten.symm rc).1 : ℕ) * chunkLen + ((flatten.symm rc).2.2 : ℕ) = (rc.2 : ℕ))
    (chunk : Fin nc) (column : Fin (width chunk)) (i : Fin n) :
    ((Keygen.permPolysOf k cs ops).getD
        ((flatten ⟨chunk, i, column⟩).2 : ℕ) []).getD (i : ℕ) 0 =
      chunkRowName (omegaOf k) deltaFp chunkLen
        ((chunkPermutationOfFlat flatten
            ((Equiv.prodComm _ _).permCongr (replayKeygenPermutation copies'))
          ⟨chunk, i, column⟩).1 : ℕ)
        ((chunkPermutationOfFlat flatten
            ((Equiv.prodComm _ _).permCongr (replayKeygenPermutation copies'))
          ⟨chunk, i, column⟩).2.1 : ℕ)
        ((chunkPermutationOfFlat flatten
            ((Equiv.prodComm _ _).permCongr (replayKeygenPermutation copies'))
          ⟨chunk, i, column⟩).2.2 : ℕ) := by
  subst numCols n
  have hfst : (flatten ⟨chunk, i, column⟩).1 = i := by
    have := hrow (flatten ⟨chunk, i, column⟩)
    rw [Equiv.symm_apply_apply] at this
    exact (Fin.ext this).symm
  -- the image cell under the chunk-shaped replay
  set fs := chunkPermutationOfFlat flatten
    ((Equiv.prodComm _ _).permCongr (replayKeygenPermutation copies'))
    ⟨chunk, i, column⟩ with hfs
  -- its flat form: the replay image of `(global column, row)`, coordinates swapped
  have hfsflat : fs = flatten.symm
      (((replayKeygenPermutation copies'
          ((flatten ⟨chunk, i, column⟩).2, (flatten ⟨chunk, i, column⟩).1)).2,
        (replayKeygenPermutation copies'
          ((flatten ⟨chunk, i, column⟩).2, (flatten ⟨chunk, i, column⟩).1)).1)) := by
    rw [hfs, chunkPermutationOfFlat_apply]
    rfl
  have hentry := permPolysOf_getD_eq cs ops copies' hcopies
    (flatten ⟨chunk, i, column⟩).2 i
  rw [show ((flatten ⟨chunk, i, column⟩).2, i) =
      ((flatten ⟨chunk, i, column⟩).2, (flatten ⟨chunk, i, column⟩).1) by
    rw [hfst]] at hentry
  rw [hentry, chunkRowName, rowName]
  rw [hfsflat]
  rw [hrow, hcol]
  ring

/-- Same-cycle facts transport from the full-domain keygen permutation to its
active-row restriction: the restriction equation pushes powers through the widening,
and widening is injective. -/
theorem sameCycle_restrict_of_widen
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hactive : activeRows ≤ domainSize)
    (fullSigma : Perm (ChunkCell nc domainSize width))
    (sigma : Perm (ChunkCell nc activeRows width))
    (hrestrict : ∀ c : ChunkCell nc activeRows width,
      widenPermutationChunkCell hactive (sigma c) =
        fullSigma (widenPermutationChunkCell hactive c))
    {c d : ChunkCell nc activeRows width}
    (h : fullSigma.SameCycle (widenPermutationChunkCell hactive c)
      (widenPermutationChunkCell hactive d)) :
    sigma.SameCycle c d := by
  classical
  have hpow : ∀ (t : ℕ) (e : ChunkCell nc activeRows width),
      (fullSigma ^ t) (widenPermutationChunkCell hactive e) =
        widenPermutationChunkCell hactive ((sigma ^ t) e) := by
    intro t
    induction t with
    | zero => intro e; rfl
    | succ t ih =>
        intro e
        rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          ← hrestrict e, ih (sigma e)]
  obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
  rw [hpow i c] at hi
  have hcd : (sigma ^ i) c = d :=
    widenPermutationChunkCell_injective hactive hi
  exact ⟨(i : ℤ), by simpa using hcd⟩

/-- Same-cycle facts transport through a conjugating equivalence: the conjugated
permutation's powers are the conjugates of the powers. -/
theorem sameCycle_permCongr_iff {α β : Type*} [DecidableEq α] [Fintype α]
    [DecidableEq β] [Fintype β] (e : α ≃ β) (π : Perm α) (x y : β) :
    (e.permCongr π).SameCycle x y ↔ π.SameCycle (e.symm x) (e.symm y) := by
  have hpow : ∀ (t : ℕ) (z : β),
      ((e.permCongr π) ^ t) z = e ((π ^ t) (e.symm z)) := by
    intro t
    induction t with
    | zero => intro z; simp
    | succ t ih =>
        intro z
        rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          Equiv.permCongr_apply, ih (e (π (e.symm z)))]
        simp
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
    refine ⟨(i : ℤ), ?_⟩
    rw [hpow i x] at hi
    have := congrArg e.symm hi
    simpa using this
  · intro h
    obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
    refine ⟨(i : ℤ), ?_⟩
    have := congrArg e hi
    rw [← hpow i x] at this
    simpa using this

/-- **Copy-pair value agreement from copy-list membership.** A copy pair of the keygen
copy list links its endpoints through the abstract replay; conjugating through the
chunk flattening, restricting to the active rows, and applying the resolver copy
theorem yields equal committed values at the two cells. This is the per-pair fact the
copy-replay witness consumes, with every coordinate translation explicit. -/
theorem chunkRowValue_eq_of_mem_copies
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (l0 lLast lBlind : CPoly) (p : Fin numProofs) {n m : ℕ}
    (h : ConstraintSatisfaction
      (constraintModelOfResolver (numProofs := numProofs) vk ch poly
        (permutationSetsOfResolver (numProofs := numProofs) vk poly)
        (permutationChunksOfResolver (numProofs := numProofs) vk poly)
        l0 lLast lBlind) n)
    (hdom : ResolverPermutationDomain vk l0 lLast lBlind n m)
    (hcycle : ResolverPermutationCycle vk poly p m)
    (hgood : ResolverPermutationGoodChallenges vk ch poly p m)
    {numCols domainSize : ℕ} (hactive : m ≤ domainSize)
    (copies' : List (FlatCell numCols domainSize × FlatCell numCols domainSize))
    (flatten : ResolverPermutationCell vk poly p domainSize ≃
      Fin domainSize × Fin numCols)
    (hrestrict : ∀ c : ResolverPermutationCell vk poly p m,
      widenPermutationChunkCell hactive (hcycle.sigma c) =
        chunkPermutationOfFlat flatten
          ((Equiv.prodComm (Fin numCols) (Fin domainSize)).permCongr
            (replayKeygenPermutation copies'))
          (widenPermutationChunkCell hactive c))
    (l r : FlatCell numCols domainSize) (hmem : (l, r) ∈ copies')
    (cl cr : ResolverPermutationCell vk poly p m)
    (hl : flatten (widenPermutationChunkCell hactive cl) = (l.2, l.1))
    (hr : flatten (widenPermutationChunkCell hactive cr) = (r.2, r.1)) :
    chunkRowValue vk.omega (ResolverPermutationPairs vk poly p)
        cl.1 cl.2.1 cl.2.2 =
      chunkRowValue vk.omega (ResolverPermutationPairs vk poly p)
        cr.1 cr.2.1 cr.2.2 := by
  classical
  -- the replay links the endpoints
  have hflat : (replayKeygenPermutation copies').SameCycle l r :=
    replayKeygenPermutation_pair_linked copies' hmem
  -- conjugate to the row-major orientation
  have hswapped :
      (((Equiv.prodComm (Fin numCols) (Fin domainSize)).permCongr
        (replayKeygenPermutation copies'))).SameCycle (l.2, l.1) (r.2, r.1) := by
    rw [sameCycle_permCongr_iff]
    simpa using hflat
  -- conjugate through the chunk flattening
  have hchunk :
      (chunkPermutationOfFlat flatten
        ((Equiv.prodComm (Fin numCols) (Fin domainSize)).permCongr
          (replayKeygenPermutation copies'))).SameCycle
        (widenPermutationChunkCell hactive cl)
        (widenPermutationChunkCell hactive cr) := by
    have hcongr :
        chunkPermutationOfFlat flatten
            ((Equiv.prodComm (Fin numCols) (Fin domainSize)).permCongr
              (replayKeygenPermutation copies')) =
          flatten.symm.permCongr
            ((Equiv.prodComm (Fin numCols) (Fin domainSize)).permCongr
              (replayKeygenPermutation copies')) := by
      refine Equiv.ext fun c => ?_
      simp [chunkPermutationOfFlat, Equiv.permCongr_apply]
    rw [hcongr, sameCycle_permCongr_iff]
    simpa [hl, hr] using hswapped
  -- restrict to the active rows and read the copy theorem
  exact ConstraintSatisfaction.resolverPermutationCopyConstraints
    vk ch poly l0 lLast lBlind p h hdom hcycle hgood
    (sameCycle_restrict_of_widen hactive _ hcycle.sigma hrestrict hchunk)

/-- Re-widening a row-bounded cell reproduces it. -/
theorem widen_mk_of_lt
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hactive : activeRows ≤ domainSize)
    (x : ChunkCell nc domainSize width) (hx : (x.2.1 : ℕ) < activeRows) :
    widenPermutationChunkCell hactive
        (⟨x.1, ⟨(x.2.1 : ℕ), hx⟩, x.2.2⟩ : ChunkCell nc activeRows width) = x := by
  rcases x with ⟨a, r, col⟩
  rfl

/-- Restrict a full-domain cell permutation to the active rows, given that it maps
active cells to active cells: injectivity survives the restriction, and a finite
injection is a permutation. -/
def restrictActivePerm
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hactive : activeRows ≤ domainSize)
    (π : Perm (ChunkCell nc domainSize width))
    (hpres : ∀ c : ChunkCell nc activeRows width,
      ((π (widenPermutationChunkCell hactive c)).2.1 : ℕ) < activeRows) :
    Perm (ChunkCell nc activeRows width) := by
  let forward : ChunkCell nc activeRows width → ChunkCell nc activeRows width :=
    fun c =>
      ⟨(π (widenPermutationChunkCell hactive c)).1,
        ⟨((π (widenPermutationChunkCell hactive c)).2.1 : ℕ), hpres c⟩,
        (π (widenPermutationChunkCell hactive c)).2.2⟩
  have hforwardWiden (c : ChunkCell nc activeRows width) :
      widenPermutationChunkCell hactive (forward c) =
        π (widenPermutationChunkCell hactive c) := by
    exact widen_mk_of_lt hactive _ (hpres c)
  have hforwardInjective : Function.Injective forward := by
    intro c d h
    apply widenPermutationChunkCell_injective hactive
    apply π.injective
    rw [← hforwardWiden c, ← hforwardWiden d, h]
  have hforwardSurjective : Function.Surjective forward :=
    (Finite.injective_iff_bijective.mp hforwardInjective).2
  have hinversePres (c : ChunkCell nc activeRows width) :
      (((π.symm (widenPermutationChunkCell hactive c)).2.1 : ℕ) < activeRows) := by
    obtain ⟨d, rfl⟩ := hforwardSurjective c
    rw [hforwardWiden d, π.symm_apply_apply]
    exact d.2.1.isLt
  let inverse : ChunkCell nc activeRows width → ChunkCell nc activeRows width :=
    fun c =>
      ⟨(π.symm (widenPermutationChunkCell hactive c)).1,
        ⟨((π.symm (widenPermutationChunkCell hactive c)).2.1 : ℕ), hinversePres c⟩,
        (π.symm (widenPermutationChunkCell hactive c)).2.2⟩
  have hinverseWiden (c : ChunkCell nc activeRows width) :
      widenPermutationChunkCell hactive (inverse c) =
        π.symm (widenPermutationChunkCell hactive c) := by
    exact widen_mk_of_lt hactive _ (hinversePres c)
  exact
    { toFun := forward
      invFun := inverse
      left_inv := fun c => widenPermutationChunkCell_injective hactive (by
        rw [hinverseWiden, hforwardWiden, π.symm_apply_apply])
      right_inv := fun c => widenPermutationChunkCell_injective hactive (by
        rw [hforwardWiden, hinverseWiden, π.apply_symm_apply]) }

/-- The restriction equation of `restrictActivePerm`, by construction. -/
theorem restrictActivePerm_widen
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hactive : activeRows ≤ domainSize)
    (π : Perm (ChunkCell nc domainSize width))
    (hpres : ∀ c : ChunkCell nc activeRows width,
      ((π (widenPermutationChunkCell hactive c)).2.1 : ℕ) < activeRows)
    (c : ChunkCell nc activeRows width) :
    widenPermutationChunkCell hactive (restrictActivePerm hactive π hpres c) =
      π (widenPermutationChunkCell hactive c) :=
  widen_mk_of_lt hactive _ (hpres c)

/-- Chunk cells are determined by their three numeric coordinates. -/
theorem chunkCell_ext {nc m : ℕ} {width : ℕ → ℕ} {x y : ChunkCell nc m width}
    (h1 : (x.1 : ℕ) = (y.1 : ℕ)) (h2 : (x.2.1 : ℕ) = (y.2.1 : ℕ))
    (h3 : (x.2.2 : ℕ) = (y.2.2 : ℕ)) : x = y := by
  rcases x with ⟨a, r, col⟩
  rcases y with ⟨b, s, dol⟩
  simp only at h1 h2 h3
  obtain rfl : a = b := Fin.ext h1
  obtain rfl : r = s := Fin.ext h2
  obtain rfl : col = dol := Fin.ext h3
  rfl

/-- The chunk flattening: halo2 groups the permutation columns into `nc` chunks of
`chunkLen` (the last possibly shorter), so a chunk cell is a `(row, global column)`
pair with `global = chunk · chunkLen + column`. Generic over the chunking law. -/
def chunkFlatten (nc numCols chunkLen m : ℕ) (width : ℕ → ℕ)
    (hcl : 0 < chunkLen) (hcover : numCols ≤ nc * chunkLen)
    (hw : ∀ c : Fin nc, width (c : ℕ) = min chunkLen (numCols - (c : ℕ) * chunkLen)) :
    ChunkCell nc m width ≃ Fin m × Fin numCols where
  toFun cell :=
    (cell.2.1, ⟨(cell.1 : ℕ) * chunkLen + (cell.2.2 : ℕ), by
      have hcol : (cell.2.2 : ℕ) < min chunkLen (numCols - (cell.1 : ℕ) * chunkLen) := by
        rw [← hw cell.1]
        exact cell.2.2.isLt
      have := lt_min_iff.mp hcol
      omega⟩)
  invFun rg :=
    ⟨⟨(rg.2 : ℕ) / chunkLen, by
        have hlt := rg.2.isLt
        by_contra hge
        push Not at hge
        have hmul : nc * chunkLen ≤ (rg.2 : ℕ) / chunkLen * chunkLen :=
          Nat.mul_le_mul_right _ hge
        have hdivle := Nat.div_mul_le_self (rg.2 : ℕ) chunkLen
        omega⟩,
      rg.1,
      ⟨(rg.2 : ℕ) % chunkLen, by
        rw [hw]
        change (rg.2 : ℕ) % chunkLen <
          min chunkLen (numCols - (rg.2 : ℕ) / chunkLen * chunkLen)
        refine lt_min (Nat.mod_lt _ hcl) ?_
        have hlt := rg.2.isLt
        have hdm := Nat.div_add_mod (rg.2 : ℕ) chunkLen
        have hcomm : (rg.2 : ℕ) / chunkLen * chunkLen =
            chunkLen * ((rg.2 : ℕ) / chunkLen) := Nat.mul_comm _ _
        omega⟩⟩
  left_inv cell := by
    rcases cell with ⟨c, i, col⟩
    have hcol : (col : ℕ) < min chunkLen (numCols - (c : ℕ) * chunkLen) := by
      rw [← hw c]
      exact col.isLt
    have hcolcl : (col : ℕ) < chunkLen := lt_of_lt_of_le hcol (min_le_left _ _)
    refine chunkCell_ext ?_ rfl ?_
    · show ((c : ℕ) * chunkLen + (col : ℕ)) / chunkLen = (c : ℕ)
      rw [Nat.mul_comm (c : ℕ) chunkLen, Nat.mul_add_div hcl,
        Nat.div_eq_of_lt hcolcl, Nat.add_zero]
    · show ((c : ℕ) * chunkLen + (col : ℕ)) % chunkLen = (col : ℕ)
      rw [Nat.mul_comm (c : ℕ) chunkLen, Nat.mul_add_mod,
        Nat.mod_eq_of_lt hcolcl]
  right_inv rg := by
    rcases rg with ⟨i, g⟩
    refine Prod.ext_iff.mpr ⟨rfl, Fin.ext ?_⟩
    show (g : ℕ) / chunkLen * chunkLen + (g : ℕ) % chunkLen = (g : ℕ)
    rw [Nat.mul_comm]
    exact Nat.div_add_mod (g : ℕ) chunkLen

@[simp]
theorem chunkFlatten_apply_row
    {nc numCols chunkLen m : ℕ} {width : ℕ → ℕ}
    (hcl : 0 < chunkLen) (hcover : numCols ≤ nc * chunkLen)
    (hw : ∀ c : Fin nc,
      width (c : ℕ) = min chunkLen (numCols - (c : ℕ) * chunkLen))
    (cell : ChunkCell nc m width) :
    (chunkFlatten nc numCols chunkLen m width hcl hcover hw cell).1 =
      cell.2.1 := rfl

@[simp]
theorem chunkFlatten_apply_column
    {nc numCols chunkLen m : ℕ} {width : ℕ → ℕ}
    (hcl : 0 < chunkLen) (hcover : numCols ≤ nc * chunkLen)
    (hw : ∀ c : Fin nc,
      width (c : ℕ) = min chunkLen (numCols - (c : ℕ) * chunkLen))
    (cell : ChunkCell nc m width) :
    ((chunkFlatten nc numCols chunkLen m width hcl hcover hw cell).2 : ℕ) =
      (cell.1 : ℕ) * chunkLen + (cell.2.2 : ℕ) := rfl

@[simp]
theorem chunkFlatten_symm_apply_row
    {nc numCols chunkLen m : ℕ} {width : ℕ → ℕ}
    (hcl : 0 < chunkLen) (hcover : numCols ≤ nc * chunkLen)
    (hw : ∀ c : Fin nc,
      width (c : ℕ) = min chunkLen (numCols - (c : ℕ) * chunkLen))
    (cell : Fin m × Fin numCols) :
    ((chunkFlatten nc numCols chunkLen m width hcl hcover hw).symm cell).2.1 =
      cell.1 := rfl

@[simp]
theorem chunkFlatten_symm_apply_column
    {nc numCols chunkLen m : ℕ} {width : ℕ → ℕ}
    (hcl : 0 < chunkLen) (hcover : numCols ≤ nc * chunkLen)
    (hw : ∀ c : Fin nc,
      width (c : ℕ) = min chunkLen (numCols - (c : ℕ) * chunkLen))
    (cell : Fin m × Fin numCols) :
    (((chunkFlatten nc numCols chunkLen m width hcl hcover hw).symm cell).1 :
        ℕ) *
        chunkLen +
        (((chunkFlatten nc numCols chunkLen m width hcl hcover hw).symm cell).2.2 :
          ℕ) =
      (cell.2 : ℕ) := by
  change (cell.2 : ℕ) / chunkLen * chunkLen +
      (cell.2 : ℕ) % chunkLen = (cell.2 : ℕ)
  rw [Nat.mul_comm]
  exact Nat.div_add_mod (cell.2 : ℕ) chunkLen

end Layout.Asm

end Zcash.Snark
