import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Probability.Distributions.Uniform

/-!
# Uniform-measure lemmas

Distribution facts about `PMF.uniformOfFintype`, kept independent of any extraction strategy:
pushforwards along equivalences and injections, product and fibre bounds, and point and blind-set
measures.

These are factored into a standalone module so the straight-line consumers
(`Soundness.GoodChallenge`, `Soundness.Multiopen.*`, `Security.KeyBinding.Probability`, and
`Soundness.AGM.*`) depend only on the distribution facts they use.
-/

namespace Zcash.Snark

open scoped ENNReal

variable {α : Type*}

/-- A finite event under the uniform distribution has probability `|E| / |α|`. -/
theorem uniformOfFintype_toOuterMeasure_finset [Fintype α] [Nonempty α] (E : Finset α) :
    (PMF.uniformOfFintype α).toOuterMeasure E = (E.card : ℝ≥0∞) / Fintype.card α := by
  rw [PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- A bijection maps the uniform distribution on `A` to the uniform distribution on `B`. -/
theorem map_uniformOfFintype_equiv {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (e : A ≃ B) : (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  refine PMF.ext (fun b => ?_)
  rw [PMF.map_apply, tsum_eq_single (e.symm b) (fun a ha => ?_)]
  · simp only [PMF.uniformOfFintype_apply, Equiv.apply_symm_apply, if_pos, Fintype.card_congr e]
  · rw [if_neg]
    intro hb
    exact ha (e.injective ((e.apply_symm_apply b).symm ▸ hb.symm))

/-- Reading a uniform random function at finitely many distinct points gives independent uniform
answers. -/
theorem uniformOfFintype_map_eval_injective {ι T α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq T]
    [Fintype α] [Nonempty α] (φ : ι → T) (hφ : Function.Injective φ) :
    (PMF.uniformOfFintype (↥(Set.range φ) → α)).map (fun O i => O (Equiv.ofInjective φ hφ i))
      = PMF.uniformOfFintype (ι → α) :=
  map_uniformOfFintype_equiv (Equiv.arrowCongr (Equiv.ofInjective φ hφ).symm (Equiv.refl α))

/-- The first component of a uniform draw on `A × B` is uniform on `A`. -/
theorem map_fst_uniformOfFintype {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (PMF.uniformOfFintype (A × B)).map Prod.fst = PMF.uniformOfFintype A := by
  classical
  refine PMF.ext fun a => ?_
  rw [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (Or.inl (ENNReal.natCast_ne_top _)),
    mul_comm ((Fintype.card A : ℝ≥0∞))⁻¹ ((Fintype.card B : ℝ≥0∞))⁻¹, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), one_mul]

/-- Reading a uniform table at distinct points gives a uniform answer vector. -/
theorem uniformOfFintype_map_precomp_injective {ι T F : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (φ : ι → T) (hφ : Function.Injective φ) :
    (PMF.uniformOfFintype (T → F)).map (fun O => O ∘ φ) = PMF.uniformOfFintype (ι → F) := by
  have hsplit : (fun O : T → F => O ∘ φ)
      = (fun O' : ↥(Set.range φ) → F => fun i => O' (Equiv.ofInjective φ hφ i))
        ∘ Prod.fst
        ∘ (Equiv.piEquivPiSubtypeProd (fun t => t ∈ Set.range φ) (fun _ => F)) := by
    funext O
    rfl
  rw [hsplit, ← PMF.map_comp, ← PMF.map_comp,
    map_uniformOfFintype_equiv (Equiv.piEquivPiSubtypeProd (fun t => t ∈ Set.range φ) (fun _ => F)),
    map_fst_uniformOfFintype, uniformOfFintype_map_eval_injective φ hφ]

/-- A set's uniform measure is its counting fraction. -/
theorem uniformOfFintype_toOuterMeasure_set {α : Type*} [Fintype α] [Nonempty α] (s : Set α) :
    (PMF.uniformOfFintype α).toOuterMeasure s = (Nat.card s : ℝ≥0∞) / Fintype.card α := by
  classical
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card',
    ← uniformOfFintype_toOuterMeasure_finset, Set.coe_toFinset]

open Classical in
/-- A uniform product inherits a bound that holds on every first-coordinate fiber. -/
theorem uniformOfFintype_prod_fiber_bound {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    [Nonempty B] (S : B → Set A) {β : ℝ≥0∞}
    (hS : ∀ b, (PMF.uniformOfFintype A).toOuterMeasure (S b) ≤ β) :
    (PMF.uniformOfFintype (A × B)).toOuterMeasure {x : A × B | x.1 ∈ S x.2} ≤ β := by
  rw [uniformOfFintype_toOuterMeasure_set]
  have hcard : (Nat.card {x : A × B | x.1 ∈ S x.2}) = ∑ b : B, Nat.card (S b) := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf,
      Finset.card_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', ← Finset.card_filter]
    congr 1
    ext a
    simp [Set.mem_toFinset]
  have hfib : ∀ b : B, ((Nat.card (S b) : ℕ) : ℝ≥0∞) ≤ β * Fintype.card A := by
    intro b
    have h := hS b
    rw [uniformOfFintype_toOuterMeasure_set, ENNReal.div_le_iff
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)] at h
    exact h
  rw [ENNReal.div_le_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    hcard]
  push_cast
  calc (∑ b : B, ((Nat.card (S b) : ℕ) : ℝ≥0∞))
      ≤ ∑ _b : B, β * Fintype.card A := Finset.sum_le_sum fun b _ => hfib b
    _ = Fintype.card B * (β * Fintype.card A) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = β * ((Fintype.card A : ℝ≥0∞) * Fintype.card B) := by ring
    _ = β * (Fintype.card (A × B)) := by rw [Fintype.card_prod]; push_cast; ring

open Classical in
/-- The symmetric Fubini bound, with the second coordinate chosen by the first. -/
theorem uniformOfFintype_prod_fiber_bound_right {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (S : A → Set B) {β : ℝ≥0∞}
    (hS : ∀ a, (PMF.uniformOfFintype B).toOuterMeasure (S a) ≤ β) :
    (PMF.uniformOfFintype (A × B)).toOuterMeasure {x : A × B | x.2 ∈ S x.1} ≤ β := by
  rw [uniformOfFintype_toOuterMeasure_set]
  have hcard : (Nat.card {x : A × B | x.2 ∈ S x.1}) = ∑ a : A, Nat.card (S a) := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf,
      Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', ← Finset.card_filter]
    congr 1
    ext b
    simp [Set.mem_toFinset]
  have hfib : ∀ a : A, ((Nat.card (S a) : ℕ) : ℝ≥0∞) ≤ β * Fintype.card B := by
    intro a
    have h := hS a
    rw [uniformOfFintype_toOuterMeasure_set, ENNReal.div_le_iff
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)] at h
    exact h
  rw [ENNReal.div_le_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _), hcard]
  push_cast
  calc (∑ a : A, ((Nat.card (S a) : ℕ) : ℝ≥0∞))
      ≤ ∑ _a : A, β * Fintype.card B := Finset.sum_le_sum fun a _ => hfib a
    _ = Fintype.card A * (β * Fintype.card B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = β * ((Fintype.card A : ℝ≥0∞) * Fintype.card B) := by ring
    _ = β * Fintype.card (A × B) := by rw [Fintype.card_prod]; push_cast; ring

/-- Unread oracle coordinates remain uniform after choosing a target from the other coordinates. -/
theorem uniformOfFintype_fresh_read_bound {ι T F X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (φ : ι → T) (hφ : Function.Injective φ)
    (choice : ({t : T // ¬ t ∈ Set.range φ} → F) → X)
    (S : X → Set (ι → F)) {β : ℝ≥0∞}
    (hS : ∀ x, (PMF.uniformOfFintype (ι → F)).toOuterMeasure (S x) ≤ β) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | (fun i => O (φ i)) ∈ S (choice (fun t => O t.1))} ≤ β := by
  have he : {O : T → F | (fun i => O (φ i)) ∈ S (choice (fun t => O t.1))}
      = (Equiv.piEquivPiSubtypeProd (fun t => t ∈ Set.range φ) (fun _ => F)) ⁻¹'
          {y : ({t : T // t ∈ Set.range φ} → F) × ({t : T // ¬ t ∈ Set.range φ} → F) |
            (fun i => y.1 (Equiv.ofInjective φ hφ i)) ∈ S (choice y.2)} := rfl
  rw [he, ← PMF.toOuterMeasure_map_apply,
    map_uniformOfFintype_equiv (Equiv.piEquivPiSubtypeProd (fun t => t ∈ Set.range φ) (fun _ => F))]
  refine uniformOfFintype_prod_fiber_bound
    (fun b => {a : {t : T // t ∈ Set.range φ} → F |
      (fun i => a (Equiv.ofInjective φ hφ i)) ∈ S (choice b)}) (fun b => ?_)
  have hpre : {a : {t : T // t ∈ Set.range φ} → F |
      (fun i => a (Equiv.ofInjective φ hφ i)) ∈ S (choice b)}
      = (fun (a : {t : T // t ∈ Set.range φ} → F) (i : ι) => a (Equiv.ofInjective φ hφ i)) ⁻¹'
          S (choice b) := rfl
  beta_reduce
  rw [hpre, ← PMF.toOuterMeasure_map_apply, uniformOfFintype_map_eval_injective φ hφ]
  exact hS (choice b)

/-- Uniform measure of a rectangle: the product of the sides' measures. -/
theorem uniformOfFintype_toOuterMeasure_prod {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    [Nonempty B] (s : Set A) (t : Set B) :
    (PMF.uniformOfFintype (A × B)).toOuterMeasure (s ×ˢ t)
      = (PMF.uniformOfFintype A).toOuterMeasure s * (PMF.uniformOfFintype B).toOuterMeasure t := by
  rw [uniformOfFintype_toOuterMeasure_set, uniformOfFintype_toOuterMeasure_set,
    uniformOfFintype_toOuterMeasure_set, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq, Set.ncard_prod, Fintype.card_prod]
  push_cast
  rw [ENNReal.mul_div_mul_comm (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    (Or.inl (ENNReal.natCast_ne_top _))]

/-- Uniform measure of the whole space is `1`. -/
theorem uniformOfFintype_toOuterMeasure_univ {α : Type*} [Fintype α] [Nonempty α] :
    (PMF.uniformOfFintype α).toOuterMeasure (Set.univ : Set α) = 1 := by
  rw [uniformOfFintype_toOuterMeasure_set, Nat.card_coe_set_eq, Set.ncard_univ,
    Nat.card_eq_fintype_card, ENNReal.div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)]

/-- Uniform measure of a singleton: `1 / |α|`. -/
theorem uniformOfFintype_toOuterMeasure_singleton {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    (PMF.uniformOfFintype α).toOuterMeasure {a} = 1 / Fintype.card α := by
  rw [uniformOfFintype_toOuterMeasure_set, Nat.card_coe_set_eq, Set.ncard_singleton, Nat.cast_one]

/-- Reading one point of a uniform table gives a uniform value. -/
theorem map_eval_uniformOfFintype {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] (t : T) :
    (PMF.uniformOfFintype (T → F)).map (fun O => O t) = PMF.uniformOfFintype F := by
  have h : (fun O : T → F => O t)
      = (Equiv.funUnique {x : T // x = t} F)
        ∘ Prod.fst
        ∘ (Equiv.piEquivPiSubtypeProd (fun x => x = t) (fun _ => F)) := by
    funext O; rfl
  rw [h, ← PMF.map_comp, ← PMF.map_comp,
    map_uniformOfFintype_equiv (Equiv.piEquivPiSubtypeProd (fun x => x = t) (fun _ => F)),
    map_fst_uniformOfFintype, map_uniformOfFintype_equiv (Equiv.funUnique {x : T // x = t} F)]

/-- A uniform table's answer at one point has the uniform marginal. -/
theorem uniformOfFintype_point_measure {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] (t : T) (s : Set F) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure {O : T → F | O t ∈ s}
      = (PMF.uniformOfFintype F).toOuterMeasure s := by
  have h : {O : T → F | O t ∈ s} = (fun O : T → F => O t) ⁻¹' s := rfl
  rw [h, ← PMF.toOuterMeasure_map_apply, map_eval_uniformOfFintype]

/-- Conditioning an update-invariant event on `O t = u` costs `1/|F|`. -/
theorem uniformOfFintype_cond_point {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] (t : T) (u : F) (E : Set (T → F))
    (hE : ∀ (O : T → F) (v : F), Function.update O t v ∈ E ↔ O ∈ E) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure {O : T → F | O t = u ∧ O ∈ E}
      = (PMF.uniformOfFintype (T → F)).toOuterMeasure E / Fintype.card F := by
  set e := Equiv.piSplitAt t (fun _ : T => F) with he
  have hsymm : ∀ (O : T → F) (v : F), e.symm (v, (e O).2) = Function.update O t v := by
    intro O v
    funext j
    by_cases hj : j = t
    · subst hj; simp [he, Equiv.piSplitAt, Function.update]
    · simp [he, Equiv.piSplitAt, Function.update, hj]
  have hEinv : ∀ (O : T → F) (v : F), (e.symm (v, (e O).2) ∈ E) ↔ O ∈ E := by
    intro O v; rw [hsymm]; exact hE O v
  have h1 : {O : T → F | O t = u ∧ O ∈ E}
      = e ⁻¹' (({u} : Set F) ×ˢ {g | e.symm (u, g) ∈ E}) := by
    ext O
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ⟨fun ⟨hu, hO⟩ => ⟨hu, (hEinv O u).mpr hO⟩, fun ⟨hu, hO⟩ => ⟨hu, (hEinv O u).mp hO⟩⟩
  have h2 : E = e ⁻¹' ((Set.univ : Set F) ×ˢ {g | e.symm (u, g) ∈ E}) := by
    ext O
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, Set.mem_setOf_eq]
    exact (hEinv O u).symm
  rw [h1, ← PMF.toOuterMeasure_map_apply, map_uniformOfFintype_equiv e,
    uniformOfFintype_toOuterMeasure_prod, uniformOfFintype_toOuterMeasure_singleton]
  conv_rhs => rw [h2, ← PMF.toOuterMeasure_map_apply, map_uniformOfFintype_equiv e,
    uniformOfFintype_toOuterMeasure_prod, uniformOfFintype_toOuterMeasure_univ]
  rw [one_mul, one_div, div_eq_mul_inv, mul_comm]

open Classical in
/-- Bound the expected size of a table-chosen set by its uniform-measure bound. -/
theorem sum_point_mem_measure_le {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] (S : (T → F) → Set F) {ε : ℝ≥0∞}
    (hS : ∀ O, (PMF.uniformOfFintype F).toOuterMeasure (S O) ≤ ε) :
    (∑ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure {O : T → F | u ∈ S O})
      ≤ ε * Fintype.card F := by
  have hcount : (∑ u : F, (Nat.card {O : T → F | u ∈ S O} : ℝ≥0∞))
      = ∑ O : T → F, (Nat.card (S O) : ℝ≥0∞) := by
    norm_cast
    calc (∑ u : F, Nat.card {O : T → F | u ∈ S O})
        = ∑ u : F, (Finset.univ.filter (fun O : T → F => u ∈ S O)).card := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
      _ = ∑ u : F, ∑ O : T → F, if u ∈ S O then 1 else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.card_filter]
      _ = ∑ O : T → F, ∑ u : F, if u ∈ S O then 1 else 0 := Finset.sum_comm
      _ = ∑ O : T → F, Nat.card (S O) := by
          refine Finset.sum_congr rfl fun O _ => ?_
          rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card',
            show (S O).toFinset = Finset.univ.filter (fun u => u ∈ S O) from by
              ext u; simp [Set.mem_toFinset],
            Finset.card_filter]
  have hper : ∀ O : T → F, (Nat.card (S O) : ℝ≥0∞) ≤ ε * Fintype.card F := by
    intro O
    have h := hS O
    rw [uniformOfFintype_toOuterMeasure_set, ENNReal.div_le_iff
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)] at h
    exact h
  calc (∑ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure {O : T → F | u ∈ S O})
      = ∑ u : F, (Nat.card {O : T → F | u ∈ S O} : ℝ≥0∞) / Fintype.card (T → F) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [uniformOfFintype_toOuterMeasure_set]
    _ = (∑ u : F, (Nat.card {O : T → F | u ∈ S O} : ℝ≥0∞)) / Fintype.card (T → F) := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = (∑ O : T → F, (Nat.card (S O) : ℝ≥0∞)) / Fintype.card (T → F) := by rw [hcount]
    _ ≤ (∑ _O : T → F, ε * Fintype.card F) / Fintype.card (T → F) := by
        gcongr with O _
        exact hper O
    _ = (Fintype.card (T → F) * (ε * Fintype.card F)) / Fintype.card (T → F) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ε * Fintype.card F := by
        rw [mul_comm ((Fintype.card (T → F) : ℝ≥0∞)),
          ENNReal.mul_div_cancel_right (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _)]

/-- An update-blind set contains `O t` with at most its uniform-measure bound. -/
theorem uniformOfFintype_point_mem_blind_le {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] (t : T) (S : (T → F) → Set F)
    (hblind : ∀ (O : T → F) (v : F), S (Function.update O t v) = S O) {ε : ℝ≥0∞}
    (hS : ∀ O, (PMF.uniformOfFintype F).toOuterMeasure (S O) ≤ ε) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure {O : T → F | O t ∈ S O} ≤ ε := by
  have hsub : {O : T → F | O t ∈ S O}
      ⊆ ⋃ u : F, {O : T → F | O t = u ∧ O ∈ {O' : T → F | u ∈ S O'}} := by
    intro O hO
    exact Set.mem_iUnion.mpr ⟨O t, rfl, hO⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  have hper : ∀ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | O t = u ∧ O ∈ {O' : T → F | u ∈ S O'}}
      = (PMF.uniformOfFintype (T → F)).toOuterMeasure {O' : T → F | u ∈ S O'}
          / Fintype.card F := by
    intro u
    refine uniformOfFintype_cond_point t u _ fun O v => ?_
    simp only [Set.mem_setOf_eq, hblind O v]
  calc (∑ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure
        {O : T → F | O t = u ∧ O ∈ {O' : T → F | u ∈ S O'}})
      = (∑ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure {O' : T → F | u ∈ S O'})
          / Fintype.card F := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        exact Finset.sum_congr rfl fun u _ => by rw [hper u, div_eq_mul_inv]
    _ ≤ (ε * Fintype.card F) / Fintype.card F := by
        gcongr
        exact sum_point_mem_measure_le S hS
    _ = ε := ENNReal.mul_div_cancel_right (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _)

end Zcash.Snark
