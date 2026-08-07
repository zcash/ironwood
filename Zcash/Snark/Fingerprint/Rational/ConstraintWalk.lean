import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Zcash.Snark.Fingerprint.Rational.Representation
import Zcash.Snark.Soundness.Pricing.DegreeWalk

/-!
# The representation walk, query side: Lagrange basis, constraints, `expectedHEval`

Stages 1–4 of the coefficient walk — everything upstream of the multiopen grouping. Each
pipeline value, as a function of the sample point (`Point.toProofString`/`Point.toChallenges`
inputs over a fixed group-data template), is given a `NumeratorRep`: a polynomial numerator over
an explicit enumerated-factor denominator, with a shape/vk-polynomial degree budget.

* Stage 1 — `lagrangeBasis_l0_rep`/`_lLast_rep`/`_lBlind_rep`: the three Lagrange basis values
  over `lagDen` (the product of the `x − ωⁱ` factors at `lagrangeRotations`). The division by
  `(n : F_p)` is multiplication by a field constant, so it needs no nonvanishing hypothesis —
  representations are about form, not meaning.
* Stage 2 — `NumeratorRep.exprEval`: a gate value at degree-≤1 leaf feeds is represented at
  degree `Expr.degreeBound` over the trivial denominator (`Expr.degreeBound` transfers from the
  committed-world walk with the leaf cost at `1`).
* Stage 3 — `allExpressions_listRep`: every constraint value (gates, permutation argument,
  lookup argument) is represented over `lagDen` at the single budget `constraintValBudget`;
  `allExpressions_length` pins the list length to `constraintBudget`, the `y`-fold's degree
  ingredient.
* Stage 4 — `expectedHEval_rep`: the `y`-fold of the constraint list divided by `xⁿ − 1`,
  represented over `vanDen = lagDen · (xⁿ − 1)` at `hEvalBudget`.

The list-level plumbing runs through `ListRep`: a point-dependent list factors through a fixed
list of represented functions. Budgets are deliberately generous — only `≤` is ever proved, and
slack costs nothing (the ε denominator is `p ≈ 2²⁵⁴`).
-/

namespace Zcash.Snark

open MvPolynomial

variable {shape : Shape} {G : Type*} {vk : VerifyingKey shape Fp G}

/-! ## Toolkit extensions -/

namespace NumeratorRep

variable {den den' : MvPolynomial (ScalarSlot shape) Fp} {f g : Point shape → Fp} {a b : ℕ}

/-- Rewrite the explicit denominator along an equality. -/
theorem denCongr (h : den = den') (hf : NumeratorRep vk den f a) :
    NumeratorRep vk den' f a := h ▸ hf

/-- A `finFn` view of slot variables is represented at degree 1: in range it is the slot
variable, out of range the constant `0`. -/
theorem finFnSlot {n : ℕ} (slotOf : Fin n → ScalarSlot shape) (i : ℕ) :
    NumeratorRep vk 1 (fun pt => finFn (fun j : Fin n => pt (slotOf j)) i) 1 := by
  by_cases h : i < n
  · simpa [finFn, h] using var (vk := vk) (slotOf ⟨i, h⟩)
  · simpa [finFn, h] using (const (vk := vk) 0).mono (by omega)

/-- A product over an index range of represented factors, over the trivial denominator. -/
theorem finsetProdRange (n : ℕ) (g : ℕ → Point shape → Fp) {a : ℕ}
    (h : ∀ j, NumeratorRep vk 1 (g j) a) :
    NumeratorRep vk 1 (fun pt => ∏ j ∈ Finset.range n, g j pt) (n * a) := by
  induction n with
  | zero => simpa using const (vk := vk) 1
  | succ n ih =>
    have hstep := ih.mul (h n)
    have : NumeratorRep vk 1 (fun pt => (∏ j ∈ Finset.range n, g j pt) * g n pt)
        (n * a + a) := hstep.denCongr (one_mul 1)
    refine (this.congr_event fun pt _ => ?_).mono (by ring_nf; omega)
    rw [Finset.prod_range_succ]

end NumeratorRep

/-- A point-dependent list of field values, represented elementwise: it factors through a fixed
list of represented functions. The factoring is what lets the fold rules
(`NumeratorRep.foldl_scale_add`) and element access apply uniformly. -/
def ListRep (vk : VerifyingKey shape Fp G) (den : MvPolynomial (ScalarSlot shape) Fp)
    (l : Point shape → List Fp) (d : ℕ) : Prop :=
  ∃ fns : List (Point shape → Fp),
    (∀ pt, l pt = fns.map (· pt)) ∧ ∀ f ∈ fns, NumeratorRep vk den f d

namespace ListRep

variable {den : MvPolynomial (ScalarSlot shape) Fp} {l l' : Point shape → List Fp} {d : ℕ}

/-- The empty list. -/
theorem nil : ListRep vk den (fun _ => []) d := ⟨[], fun _ => rfl, by simp⟩

/-- A represented list factored through a constant index list. -/
theorem ofMap {α : Type*} (c : List α) (g : α → Point shape → Fp)
    (h : ∀ x ∈ c, NumeratorRep vk den (g x) d)
    (hl : ∀ pt, l pt = c.map (fun x => g x pt)) : ListRep vk den l d := by
  refine ⟨c.map g, fun pt => ?_, fun f hf => ?_⟩
  · rw [hl, List.map_map]; rfl
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf
    exact h x hx

/-- Concatenation of represented lists. -/
theorem append (h : ListRep vk den l d) (h' : ListRep vk den l' d) :
    ListRep vk den (fun pt => l pt ++ l' pt) d := by
  obtain ⟨fns, heq, hrep⟩ := h
  obtain ⟨fns', heq', hrep'⟩ := h'
  refine ⟨fns ++ fns', fun pt => ?_, fun f hf => ?_⟩
  · show l pt ++ l' pt = (fns ++ fns').map (· pt)
    rw [List.map_append, heq, heq']
  · rcases List.mem_append.mp hf with hf | hf
    · exact hrep f hf
    · exact hrep' f hf

/-- Flattened blocks over a constant index list, each block represented. -/
theorem flattenMap {α : Type*} (c : List α) (blocks : α → Point shape → List Fp)
    (h : ∀ x ∈ c, ListRep vk den (blocks x) d) :
    ListRep vk den (fun pt => (c.map (fun x => blocks x pt)).flatten) d := by
  induction c with
  | nil => simpa using nil
  | cons x t ih =>
    have hx := h x List.mem_cons_self
    have ht := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simpa using hx.append ht

/-- Weaken the degree bound. -/
theorem mono {d' : ℕ} (hd : d ≤ d') (h : ListRep vk den l d) : ListRep vk den l d' :=
  let ⟨fns, heq, hrep⟩ := h
  ⟨fns, heq, fun f hf => (hrep f hf).mono hd⟩

/-- A represented list has a point-independent length. -/
theorem length_const (h : ListRep vk den l d) (pt pt' : Point shape) :
    (l pt).length = (l pt').length := by
  obtain ⟨fns, heq, -⟩ := h
  rw [heq, heq, List.length_map, List.length_map]

end ListRep

/-! ## Budgets

Plain ℕ arithmetic over shape fields and vk atoms; only `≤` is ever proved against them. -/

/-- The largest gate degree bound in the verifying key. -/
def gateDegreeBudget (vk : VerifyingKey shape Fp G) : ℕ :=
  ((vk.gates.map Expr.degreeBound).foldr max 0)

/-- The largest lookup input/table expression degree bound in the verifying key. -/
def lookupExprBudget (vk : VerifyingKey shape Fp G) : ℕ :=
  ((List.ofFn (fun l : Fin shape.numLookups =>
    max (((vk.lookupInputExprs l).map Expr.degreeBound).foldr max 0)
      (((vk.lookupTableExprs l).map Expr.degreeBound).foldr max 0))).foldr max 0)

/-- The longest lookup input/table expression list in the verifying key. -/
def lookupLenBudget (vk : VerifyingKey shape Fp G) : ℕ :=
  ((List.ofFn (fun l : Fin shape.numLookups =>
    max (vk.lookupInputExprs l).length (vk.lookupTableExprs l).length)).foldr max 0)

/-- Degree budget for one Lagrange basis value over `lagDen`: the `xⁿ − 1` numerator plus the
factor-clearing slack. -/
def lagBudget (vk : VerifyingKey shape Fp G) : ℕ :=
  vk.n + (lagrangeRotations vk).length

/-- Degree budget for one constraint value over `lagDen` — gates, permutation rules (chunk
width priced through `vk.chunkLen`), and lookup rules (compression priced through the lookup
budgets), all under one generous cap. -/
def constraintValBudget (vk : VerifyingKey shape Fp G) : ℕ :=
  lagBudget vk + gateDegreeBudget vk + 2 * vk.chunkLen
    + 2 * (lookupExprBudget vk + lookupLenBudget vk) + 8

/-- The exact length of `allExpressions` (under the chunk-layout hypotheses): per sub-proof, the
gates, the `2·sets + 1` permutation rules, and five rules per lookup. -/
def constraintBudget (shape : Shape) (vk : VerifyingKey shape Fp G) : ℕ :=
  shape.numProofs * (vk.gates.length + (2 * shape.numPermutationSets + 1)
    + 5 * shape.numLookups)

/-- Degree budget for `expectedHEval` over `vanDen`: the constraint budget prices the `y`-fold,
the value budget each element. -/
def hEvalBudget (shape : Shape) (vk : VerifyingKey shape Fp G) : ℕ :=
  constraintValBudget vk + constraintBudget shape vk

/-! ## The two stage denominators -/

/-- The Lagrange-basis denominator: the product of the enumerated `x − ωⁱ` factors. -/
noncomputable def lagDen (vk : VerifyingKey shape Fp G) : MvPolynomial (ScalarSlot shape) Fp :=
  ((lagrangeRotations vk).map fun i => X ScalarSlot.x - C (vk.omega ^ i)).prod

/-- The vanishing denominator: `lagDen` times the `xⁿ − 1` factor. -/
noncomputable def vanDen (vk : VerifyingKey shape Fp G) : MvPolynomial (ScalarSlot shape) Fp :=
  lagDen vk * (X ScalarSlot.x ^ vk.n - 1)

/-- `lagDen` is a product of enumerated factors. -/
theorem lagDen_mem :
    lagDen vk ∈ Submonoid.closure {φ | φ ∈ denFactors vk} := by
  refine Submonoid.list_prod_mem _ fun φ hφ => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hφ
  refine Submonoid.subset_closure ?_
  simp only [Set.mem_setOf_eq, denFactors, List.mem_append]
  exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i, hi, rfl⟩)))

/-- `vanDen` is a product of enumerated factors. -/
theorem vanDen_mem :
    vanDen vk ∈ Submonoid.closure {φ | φ ∈ denFactors vk} := by
  refine Submonoid.mul_mem _ lagDen_mem (Submonoid.subset_closure ?_)
  simp [denFactors]

/-- `lagDen`'s total degree is at most the rotation count. -/
theorem lagDen_totalDegree_le :
    (lagDen vk).totalDegree ≤ (lagrangeRotations vk).length := by
  refine le_trans (totalDegree_list_prod _) ?_
  rw [List.map_map]
  have key : ∀ l : List ℤ,
      (l.map (totalDegree ∘ fun i =>
        (X ScalarSlot.x - C (vk.omega ^ i) : MvPolynomial (ScalarSlot shape) Fp))).sum
        ≤ l.length := by
    intro l
    induction l with
    | nil => simp
    | cons i t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Function.comp_apply]
      have h1 : ((X ScalarSlot.x - C (vk.omega ^ i) :
          MvPolynomial (ScalarSlot shape) Fp)).totalDegree ≤ 1 := by
        refine le_trans (totalDegree_sub _ _) ?_
        simp [totalDegree_X]
      omega
  exact key _

/-- `vanDen`'s total degree is at most `lagBudget`. -/
theorem vanDen_totalDegree_le : (vanDen vk).totalDegree ≤ lagBudget vk := by
  refine le_trans (totalDegree_mul _ _) ?_
  have h2 : ((X ScalarSlot.x ^ vk.n - 1 : MvPolynomial (ScalarSlot shape) Fp)).totalDegree
      ≤ vk.n := by
    refine le_trans (totalDegree_sub _ _) ?_
    simp [totalDegree_X_pow]
  have h1 := lagDen_totalDegree_le (vk := vk)
  rw [lagBudget]
  omega

/-! ## Stage 2: gate values -/

/-- A gate value at degree-≤1 leaf feeds is represented at the gate's syntactic degree bound
over the trivial denominator — `Expr.degreeBound` with the leaf cost at `1`. -/
theorem NumeratorRep.exprEval {fE aE iE : ℕ → Point shape → Fp}
    (hf : ∀ i, NumeratorRep vk 1 (fE i) 1) (ha : ∀ i, NumeratorRep vk 1 (aE i) 1)
    (hi : ∀ i, NumeratorRep vk 1 (iE i) 1) (e : Expr Fp) :
    NumeratorRep vk 1
      (fun pt => e.eval (fun i => fE i pt) (fun i => aE i pt) (fun i => iE i pt))
      e.degreeBound := by
  induction e with
  | constant c => simpa [Expr.eval, Expr.degreeBound] using const (vk := vk) c
  | fixed i => simpa [Expr.eval, Expr.degreeBound] using hf i
  | advice i => simpa [Expr.eval, Expr.degreeBound] using ha i
  | «instance» i => simpa [Expr.eval, Expr.degreeBound] using hi i
  | negated a ih => simpa [Expr.eval, Expr.degreeBound] using ih.neg
  | sum a b iha ihb => simpa [Expr.eval, Expr.degreeBound] using iha.add ihb
  | product a b iha ihb =>
    simpa [Expr.eval, Expr.degreeBound] using (iha.mul ihb).denCongr (one_mul 1)
  | scaled a c ih =>
    simpa [Expr.eval, Expr.degreeBound] using (ih.mul (const (vk := vk) c)).denCongr (one_mul 1)

/-! ## Stage 1: the Lagrange basis values -/

/-- Sums of mapped total degrees over degree-≤1 factors are bounded by the length. -/
theorem sum_totalDegree_map_le_length :
    ∀ l : List (MvPolynomial (ScalarSlot shape) Fp),
      (∀ φ ∈ l, φ.totalDegree ≤ 1) → (l.map totalDegree).sum ≤ l.length := by
  intro l
  induction l with
  | nil => simp
  | cons φ t ih =>
    intro h
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h φ List.mem_cons_self
    have h2 := ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)
    omega

/-- Every enumerated Lagrange factor has total degree at most 1. -/
theorem lagFactor_totalDegree_le (i : ℤ) :
    ((X ScalarSlot.x - C (vk.omega ^ i) : MvPolynomial (ScalarSlot shape) Fp)).totalDegree
      ≤ 1 := by
  refine le_trans (totalDegree_sub _ _) ?_
  simp [totalDegree_X]

/-- Extend a representation over one enumerated Lagrange factor to the whole `lagDen`: the
remaining factors multiply into both sides, adding at most the rotation count to the degree. -/
theorem NumeratorRep.extendToLagDen {f : Point shape → Fp} {d : ℕ} (i : ℤ)
    (hi : i ∈ lagrangeRotations vk)
    (h : NumeratorRep vk (X ScalarSlot.x - C (vk.omega ^ i)) f d) :
    NumeratorRep vk (lagDen vk) f (d + (lagrangeRotations vk).length) := by
  classical
  set L : List (MvPolynomial (ScalarSlot shape) Fp) :=
    (lagrangeRotations vk).map fun j => X ScalarSlot.x - C (vk.omega ^ j) with hL
  have hmem : (X ScalarSlot.x - C (vk.omega ^ i) : MvPolynomial (ScalarSlot shape) Fp) ∈ L :=
    List.mem_map.mpr ⟨i, hi, rfl⟩
  have hfact := List.prod_erase hmem
  have hext := h.extend ((L.erase (X ScalarSlot.x - C (vk.omega ^ i))).prod)
  have hdeg : (((L.erase (X ScalarSlot.x - C (vk.omega ^ i))).prod)).totalDegree
      ≤ (lagrangeRotations vk).length := by
    refine le_trans (totalDegree_list_prod _) ?_
    refine le_trans (sum_totalDegree_map_le_length _ fun φ hφ => ?_) ?_
    · have hφL : φ ∈ L := List.mem_of_mem_erase hφ
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hφL
      exact lagFactor_totalDegree_le j
    · calc (L.erase (X ScalarSlot.x - C (vk.omega ^ i))).length
          ≤ L.length := (List.erase_sublist ..).length_le
        _ = (lagrangeRotations vk).length := by rw [hL, List.length_map]
  refine ((hext.mono (by omega)).denCongr ?_)
  rw [hfact]
  rfl

/-- One Lagrange basis value at an enumerated rotation, over its own `x − ωⁱ` factor. The
division by `(n : F_p)` is multiplication by a field constant — no nonvanishing needed. -/
theorem lagrangeBasisValue_rep (i : ℤ) (hi : i ∈ lagrangeRotations vk) :
    NumeratorRep vk (X ScalarSlot.x - C (vk.omega ^ i))
      (fun pt => lagrangeBasisValue vk.omega vk.n (pt ScalarSlot.x ^ vk.n) (pt ScalarSlot.x) i)
      vk.n := by
  have hfac : (X ScalarSlot.x - C (vk.omega ^ i) : MvPolynomial (ScalarSlot shape) Fp)
      ∈ denFactors vk := by
    simp only [denFactors, List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i, hi, rfl⟩)))
  have hxn : NumeratorRep vk 1 (fun pt => pt ScalarSlot.x ^ vk.n - 1) vk.n := by
    have hp := ((NumeratorRep.var (vk := vk) ScalarSlot.x).pow vk.n).denCongr (one_pow vk.n)
    simpa using (hp.sub (NumeratorRep.const 1)).mono (by omega)
  have hnum : NumeratorRep vk 1
      (fun pt => (pt ScalarSlot.x ^ vk.n - 1) * vk.omega ^ i) vk.n := by
    simpa using (hxn.mul (NumeratorRep.const (vk.omega ^ i))).denCongr (one_mul 1)
  have hdiv := (hnum.divFactor _ hfac).smul ((vk.n : Fp))⁻¹
  refine (hdiv.denCongr (one_mul _)).congr_event fun pt _ => ?_
  rw [lagrangeBasisValue]
  have heval : eval pt (X ScalarSlot.x - C (vk.omega ^ i)) = pt ScalarSlot.x - vk.omega ^ i := by
    simp
  rw [heval, div_eq_mul_inv, mul_inv]
  ring

/-- The `l₀` Lagrange basis value over `lagDen`, in the pipeline's exact spelling. -/
theorem lagrangeBasis_l0_rep :
    NumeratorRep vk (lagDen vk)
      (fun pt =>
        (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
          (pt ScalarSlot.x)).1)
      (lagBudget vk) := by
  have h0 : (0 : ℤ) ∈ lagrangeRotations vk := by simp [lagrangeRotations]
  have := (lagrangeBasisValue_rep 0 h0).extendToLagDen 0 h0
  exact this.congr_event fun pt _ => rfl

/-- The `l_last` Lagrange basis value over `lagDen`, in the pipeline's exact spelling. -/
theorem lagrangeBasis_lLast_rep :
    NumeratorRep vk (lagDen vk)
      (fun pt =>
        (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
          (pt ScalarSlot.x)).2.1)
      (lagBudget vk) := by
  have hm : -((vk.blindingFactors : ℤ) + 1) ∈ lagrangeRotations vk := by
    simp [lagrangeRotations]
  have := (lagrangeBasisValue_rep _ hm).extendToLagDen _ hm
  exact this.congr_event fun pt _ => rfl

/-- Left folds by `+` from an accumulator are the accumulator plus the sum. -/
theorem foldl_add_eq_add_sum (l : List Fp) : ∀ a : Fp, l.foldl (· + ·) a = a + l.sum := by
  induction l with
  | nil => intro a; simp
  | cons x t ih =>
    intro a
    rw [List.foldl_cons, ih, List.sum_cons]
    ring

/-- The `l_blind` Lagrange basis value over `lagDen`, in the pipeline's exact spelling: the sum
of the blinding-row basis values, each an enumerated rotation. -/
theorem lagrangeBasis_lBlind_rep :
    NumeratorRep vk (lagDen vk)
      (fun pt =>
        (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
          (pt ScalarSlot.x)).2.2)
      (lagBudget vk) := by
  have hsum := NumeratorRep.listSum (vk := vk) (den := lagDen vk) (a := lagBudget vk)
    ((List.range vk.blindingFactors).map fun j pt =>
      lagrangeBasisValue vk.omega vk.n (pt ScalarSlot.x ^ vk.n) (pt ScalarSlot.x)
        (-((j : ℤ) + 1)))
    (by
      intro f hf
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
      have hm : -((j : ℤ) + 1) ∈ lagrangeRotations vk := by
        unfold lagrangeRotations
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
      exact (lagrangeBasisValue_rep _ hm).extendToLagDen _ hm)
  refine hsum.congr_event fun pt _ => ?_
  show _ = (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
    (pt ScalarSlot.x)).2.2
  show _ = ((List.range vk.blindingFactors).map
    (fun j => lagrangeBasisValue vk.omega vk.n (pt ScalarSlot.x ^ vk.n) (pt ScalarSlot.x)
      (-((j : ℤ) + 1)))).foldl (· + ·) 0
  rw [foldl_add_eq_add_sum, zero_add, List.map_map]
  rfl

/-! ## Stage 3: the constraint list -/

/-- Elements are bounded by their `foldr max` cap. -/
theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons x t ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (ih h') (le_max_right _ _)

/-- The head of a nonempty `ofFn` list. -/
theorem head?_ofFn {n : ℕ} {α : Type*} (f : Fin n → α) (h : 0 < n) :
    (List.ofFn f).head? = some (f ⟨0, h⟩) := by
  rw [List.head?_eq_getElem?, List.getElem?_ofFn]
  simp [h]

/-- The last element of a nonempty `ofFn` list. -/
theorem getLast?_ofFn {n : ℕ} {α : Type*} (f : Fin n → α) (h : 0 < n) :
    (List.ofFn f).getLast? = some (f ⟨n - 1, by omega⟩) := by
  rw [List.getLast?_eq_getElem?, List.getElem?_ofFn]
  simp [List.length_ofFn, Nat.sub_lt h]

namespace ListRep

variable {den : MvPolynomial (ScalarSlot shape) Fp} {l l' : Point shape → List Fp} {d : ℕ}

/-- Rewrite the represented list along a pointwise equality. -/
theorem congr (h : ∀ pt, l pt = l' pt) (hl : ListRep vk den l d) : ListRep vk den l' d :=
  let ⟨fns, heq, hrep⟩ := hl
  ⟨fns, fun pt => (h pt) ▸ heq pt, hrep⟩

/-- A singleton list. -/
theorem singleton {f : Point shape → Fp} (h : NumeratorRep vk den f d) :
    ListRep vk den (fun pt => [f pt]) d :=
  ⟨[f], fun _ => rfl, by simpa using h⟩

end ListRep

/-- The three `finFn` evaluation feeds of a sub-proof, packaged: each index is represented at
degree 1 over the trivial denominator. -/
theorem finFn_feeds_rep (base : ProofString shape Fp G) (p : Fin shape.numProofs) :
    (∀ i, NumeratorRep vk 1
        (fun pt => finFn ((Point.toProofString pt base).fixedEvals) i) 1)
      ∧ (∀ i, NumeratorRep vk 1
        (fun pt => finFn ((Point.toProofString pt base).adviceEvals p) i) 1)
      ∧ (∀ i, NumeratorRep vk 1
        (fun pt => finFn ((Point.toProofString pt base).instanceEvals p) i) 1) :=
  ⟨fun i => NumeratorRep.finFnSlot (fun q => ScalarSlot.fixedEval q) i,
    fun i => NumeratorRep.finFnSlot (fun q => ScalarSlot.adviceEval p q) i,
    fun i => NumeratorRep.finFnSlot (fun q => ScalarSlot.instanceEval p q) i⟩

/-- The gate segment of a sub-proof's constraint list, represented over `lagDen` (the trivial
denominator extended, so all segments share one denominator). -/
theorem gateSeg_listRep (base : ProofString shape Fp G) (p : Fin shape.numProofs) :
    ListRep vk (lagDen vk)
      (fun pt => vk.gates.map fun g =>
        g.eval (finFn ((Point.toProofString pt base).fixedEvals))
          (finFn ((Point.toProofString pt base).adviceEvals p))
          (finFn ((Point.toProofString pt base).instanceEvals p)))
      (constraintValBudget vk) := by
  obtain ⟨hf, ha, hi⟩ := finFn_feeds_rep (vk := vk) base p
  refine ListRep.ofMap vk.gates
    (fun g pt => g.eval (finFn ((Point.toProofString pt base).fixedEvals))
      (finFn ((Point.toProofString pt base).adviceEvals p))
      (finFn ((Point.toProofString pt base).instanceEvals p)))
    (fun g hg => ?_) (fun pt => rfl)
  have hrep := NumeratorRep.exprEval hf ha hi g
  have hdb : g.degreeBound ≤ gateDegreeBudget vk :=
    le_foldr_max (List.mem_map.mpr ⟨g, hg, rfl⟩)
  have hext := (hrep.extend (lagDen vk)).denCongr (one_mul _)
  refine hext.mono ?_
  have := lagDen_totalDegree_le (vk := vk)
  simp only [constraintValBudget, lagBudget]
  omega

section PermSegment

variable (base : ProofString shape Fp G) (p : Fin shape.numProofs)
variable {l0 lLast lBlind : Point shape → Fp}

/-- The per-set `lastEval.getD 0` reading is represented at degree 1: on the non-last sets it is
the `permLastEval` slot variable, on the last set the constant `0`. -/
theorem lastEvalGetD_rep (s : Fin shape.numPermutationSets) :
    NumeratorRep vk 1
      (fun pt => ((Point.toProofString pt base).permutationSetEvals p s).lastEval.getD 0) 1 := by
  by_cases h : s.val + 1 < shape.numPermutationSets
  · refine (NumeratorRep.var (ScalarSlot.permLastEval p ⟨s.val, by omega⟩)).congr_event
      fun pt _ => ?_
    rw [toProofString_permLastEval_of_lt pt base p s h]
    rfl
  · have h' : s.val + 1 = shape.numPermutationSets := by
      have := s.isLt
      omega
    refine ((NumeratorRep.const 0).mono (by omega)).congr_event fun pt _ => ?_
    rw [toProofString_permLastEval_of_last pt base p s h']
    rfl

/-- The active-row switch `1 − (l_last + l_blind)` over `lagDen`. -/
theorem activeRow_rep (hL : NumeratorRep vk (lagDen vk) lLast (lagBudget vk))
    (hB : NumeratorRep vk (lagDen vk) lBlind (lagBudget vk)) :
    NumeratorRep vk (lagDen vk) (fun pt => 1 - (lLast pt + lBlind pt)) (lagBudget vk) := by
  have h1 : NumeratorRep vk (lagDen vk) (fun _ => (1 : Fp)) (lagBudget vk) := by
    refine ((NumeratorRep.const 1).extend (lagDen vk)).denCongr (one_mul _) |>.mono ?_
    have := lagDen_totalDegree_le (vk := vk)
    simp only [lagBudget]
    omega
  have h2 : NumeratorRep vk (lagDen vk) (fun pt => lLast pt + lBlind pt) (lagBudget vk) :=
    (hL.add hB).mono (max_self _).le
  exact (h1.sub h2).mono (max_self _).le

/-- One resolved permutation-chunk column pair, both components at degree 1. -/
theorem chunkPair_rep (cr : ColumnRef × ℕ) :
    NumeratorRep vk 1
      (fun pt => cr.1.resolve (finFn ((Point.toProofString pt base).instanceEvals p))
        (finFn ((Point.toProofString pt base).adviceEvals p))
        (finFn ((Point.toProofString pt base).fixedEvals))) 1
    ∧ NumeratorRep vk 1
      (fun pt => finFn ((Point.toProofString pt base).permutationCommonEvals) cr.2) 1 := by
  obtain ⟨hf, ha, hi⟩ := finFn_feeds_rep (vk := vk) base p
  constructor
  · cases hcr : cr.1 with
    | advice i =>
      refine (ha i).congr_event fun pt _ => ?_
      simp [ColumnRef.resolve]
    | fixed i =>
      refine (hf i).congr_event fun pt _ => ?_
      simp [ColumnRef.resolve]
    | «instance» i =>
      refine (hi i).congr_event fun pt _ => ?_
      simp [ColumnRef.resolve]
  · exact NumeratorRep.finFnSlot (fun c => ScalarSlot.permCommonEval c) cr.2

/-- One permutation chunk's step rule, represented over `lagDen`: both interior products have
degree-≤2 factors, the chunk width is priced by `vk.chunkLen`, and the active-row switch
carries the Lagrange budget. -/
theorem permChunk_rep (hL : NumeratorRep vk (lagDen vk) lLast (lagBudget vk))
    (hB : NumeratorRep vk (lagDen vk) lBlind (lagBudget vk))
    (ci : ℕ) (s : Fin shape.numPermutationSets) (layout : List (ColumnRef × ℕ))
    (hW : layout.length ≤ vk.chunkLen) :
    NumeratorRep vk (lagDen vk)
      (fun pt => permChunkExpression (pt ScalarSlot.beta) (pt ScalarSlot.gamma)
        (pt ScalarSlot.x) vk.delta vk.chunkLen ci
        ((Point.toProofString pt base).permutationSetEvals p s)
        (layout.map fun cr =>
          (cr.1.resolve (finFn ((Point.toProofString pt base).instanceEvals p))
            (finFn ((Point.toProofString pt base).adviceEvals p))
            (finFn ((Point.toProofString pt base).fixedEvals)),
          finFn ((Point.toProofString pt base).permutationCommonEvals) cr.2))
        (lLast pt) (lBlind pt))
      (1 + 2 * vk.chunkLen + lagBudget vk) := by
  classical
  set pairsF : List ((Point shape → Fp) × (Point shape → Fp)) :=
    layout.map fun cr =>
      (fun pt => cr.1.resolve (finFn ((Point.toProofString pt base).instanceEvals p))
        (finFn ((Point.toProofString pt base).adviceEvals p))
        (finFn ((Point.toProofString pt base).fixedEvals)),
      fun pt => finFn ((Point.toProofString pt base).permutationCommonEvals) cr.2) with hpairsF
  have hlenF : pairsF.length = layout.length := by rw [hpairsF, List.length_map]
  have hgetDF : ∀ j, j < layout.length →
      pairsF.getD j (fun _ => 0, fun _ => 0)
        = (fun pt => (layout.getD j (ColumnRef.fixed 0, 0)).1.resolve
            (finFn ((Point.toProofString pt base).instanceEvals p))
            (finFn ((Point.toProofString pt base).adviceEvals p))
            (finFn ((Point.toProofString pt base).fixedEvals)),
          fun pt => finFn ((Point.toProofString pt base).permutationCommonEvals)
            (layout.getD j (ColumnRef.fixed 0, 0)).2) := by
    intro j hj
    rw [hpairsF, List.getD_eq_getElem _ _ (by simpa using hj),
      List.getD_eq_getElem _ _ hj]
    simp
  have hcomp1 : ∀ j, NumeratorRep vk 1
      (fun pt => (pairsF.getD j (fun _ => 0, fun _ => 0)).1 pt) 1 := by
    intro j
    by_cases hj : j < layout.length
    · rw [hgetDF j hj]
      exact (chunkPair_rep base p _).1
    · rw [List.getD_eq_default _ _ (by omega)]
      exact (NumeratorRep.const 0).mono (by omega)
  have hcomp2 : ∀ j, NumeratorRep vk 1
      (fun pt => (pairsF.getD j (fun _ => 0, fun _ => 0)).2 pt) 1 := by
    intro j
    by_cases hj : j < layout.length
    · rw [hgetDF j hj]
      exact (chunkPair_rep base p _).2
    · rw [List.getD_eq_default _ _ (by omega)]
      exact (NumeratorRep.const 0).mono (by omega)
  -- the two product factor families, each degree ≤ 2 over the trivial denominator
  have hleftFac : ∀ j, NumeratorRep vk 1
      (fun pt => (pairsF.getD j (fun _ => 0, fun _ => 0)).1 pt
        + pt ScalarSlot.beta * (pairsF.getD j (fun _ => 0, fun _ => 0)).2 pt
        + pt ScalarSlot.gamma) 2 := by
    intro j
    have hmul := ((NumeratorRep.var (vk := vk) ScalarSlot.beta).mul (hcomp2 j)).denCongr
      (one_mul 1)
    have := ((hcomp1 j).add hmul).add (NumeratorRep.var ScalarSlot.gamma)
    exact this.mono (by omega)
  have hrightFac : ∀ j, NumeratorRep vk 1
      (fun pt => (pairsF.getD j (fun _ => 0, fun _ => 0)).1 pt
        + pt ScalarSlot.beta * pt ScalarSlot.x * vk.delta ^ (ci * vk.chunkLen) * vk.delta ^ j
        + pt ScalarSlot.gamma) 2 := by
    intro j
    have hd0 : NumeratorRep vk 1
        (fun pt => pt ScalarSlot.beta * pt ScalarSlot.x * vk.delta ^ (ci * vk.chunkLen)
          * vk.delta ^ j) 2 := by
      have h1 := ((NumeratorRep.var (vk := vk) ScalarSlot.beta).mul
        (NumeratorRep.var ScalarSlot.x)).denCongr (one_mul 1)
      have h2 := (h1.mul (NumeratorRep.const (vk.delta ^ (ci * vk.chunkLen)))).denCongr
        (one_mul 1)
      have h3 := (h2.mul (NumeratorRep.const (vk.delta ^ j))).denCongr (one_mul 1)
      exact h3.mono (by omega)
    have := ((hcomp1 j).add hd0).add (NumeratorRep.var ScalarSlot.gamma)
    exact this.mono (by omega)
  -- the two interior products
  have hleft : NumeratorRep vk 1
      (fun pt => pt (ScalarSlot.permNextEval p s)
        * ∏ j ∈ Finset.range layout.length,
          ((pairsF.getD j (fun _ => 0, fun _ => 0)).1 pt
            + pt ScalarSlot.beta * (pairsF.getD j (fun _ => 0, fun _ => 0)).2 pt
            + pt ScalarSlot.gamma)) (1 + 2 * vk.chunkLen) := by
    have hprod := NumeratorRep.finsetProdRange (vk := vk) layout.length _ hleftFac
    have := ((NumeratorRep.var (ScalarSlot.permNextEval p s)).mul hprod).denCongr (one_mul 1)
    exact this.mono (by omega)
  have hright : NumeratorRep vk 1
      (fun pt => pt (ScalarSlot.permEval p s)
        * ∏ j ∈ Finset.range layout.length,
          ((pairsF.getD j (fun _ => 0, fun _ => 0)).1 pt
            + pt ScalarSlot.beta * pt ScalarSlot.x * vk.delta ^ (ci * vk.chunkLen)
              * vk.delta ^ j
            + pt ScalarSlot.gamma)) (1 + 2 * vk.chunkLen) := by
    have hprod := NumeratorRep.finsetProdRange (vk := vk) layout.length _ hrightFac
    have := ((NumeratorRep.var (ScalarSlot.permEval p s)).mul hprod).denCongr (one_mul 1)
    exact this.mono (by omega)
  have hactive := activeRow_rep (vk := vk) hL hB
  have hdiff := hleft.sub hright
  have hres := ((hdiff.mul hactive).denCongr (one_mul _)).mono
    (a := max (1 + 2 * vk.chunkLen) (1 + 2 * vk.chunkLen) + lagBudget vk)
    (b := 1 + 2 * vk.chunkLen + lagBudget vk) (by omega)
  refine hres.congr_event fun pt _ => ?_
  set pairs : List (Fp × Fp) := layout.map fun cr =>
    (cr.1.resolve (finFn ((Point.toProofString pt base).instanceEvals p))
      (finFn ((Point.toProofString pt base).adviceEvals p))
      (finFn ((Point.toProofString pt base).fixedEvals)),
    finFn ((Point.toProofString pt base).permutationCommonEvals) cr.2) with hpairs
  rw [permChunkExpression_eq]
  have hlen' : pairs.length = layout.length := by rw [hpairs, List.length_map]
  rw [hlen']
  have hgetD : ∀ j, j ∈ Finset.range layout.length →
      pairs.getD j (0, 0)
        = ((pairsF.getD j (fun _ => 0, fun _ => 0)).1 pt,
          (pairsF.getD j (fun _ => 0, fun _ => 0)).2 pt) := by
    intro j hj
    have hj' : j < layout.length := Finset.mem_range.mp hj
    rw [hgetDF j hj', hpairs, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj'),
      List.getD_eq_getElem _ _ hj']
    simp
  have hprodL : ∏ j ∈ Finset.range layout.length,
      ((pairs.getD j (0, 0)).1 + pt ScalarSlot.beta * (pairs.getD j (0, 0)).2
        + pt ScalarSlot.gamma)
      = ∏ j ∈ Finset.range layout.length,
        ((pairsF.getD j (fun _ => 0, fun _ => 0)).1 pt
          + pt ScalarSlot.beta * (pairsF.getD j (fun _ => 0, fun _ => 0)).2 pt
          + pt ScalarSlot.gamma) :=
    Finset.prod_congr rfl fun j hj => by rw [hgetD j hj]
  have hprodR : ∏ j ∈ Finset.range layout.length,
      ((pairs.getD j (0, 0)).1
        + pt ScalarSlot.beta * pt ScalarSlot.x * vk.delta ^ (ci * vk.chunkLen) * vk.delta ^ j
        + pt ScalarSlot.gamma)
      = ∏ j ∈ Finset.range layout.length,
        ((pairsF.getD j (fun _ => 0, fun _ => 0)).1 pt
          + pt ScalarSlot.beta * pt ScalarSlot.x * vk.delta ^ (ci * vk.chunkLen) * vk.delta ^ j
          + pt ScalarSlot.gamma) :=
    Finset.prod_congr rfl fun j hj => by rw [hgetD j hj]
  rw [hprodL, hprodR]
  rfl

/-- The permutation segment of a sub-proof's constraint list, represented over `lagDen`, in the
exact spelling `subProofExpressions` produces. -/
theorem permSeg_listRep (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (h0 : NumeratorRep vk (lagDen vk) l0 (lagBudget vk))
    (hL : NumeratorRep vk (lagDen vk) lLast (lagBudget vk))
    (hB : NumeratorRep vk (lagDen vk) lBlind (lagBudget vk)) :
    ListRep vk (lagDen vk)
      (fun pt => permutationExpressions
        (List.ofFn fun s => (Point.toProofString pt base).permutationSetEvals p s)
        (((List.ofFn fun s => (Point.toProofString pt base).permutationSetEvals p s).zip
            vk.permutationChunks).map fun sc =>
          (sc.1, sc.2.map fun cr =>
            (cr.1.resolve (finFn ((Point.toProofString pt base).instanceEvals p))
              (finFn ((Point.toProofString pt base).adviceEvals p))
              (finFn ((Point.toProofString pt base).fixedEvals)),
            finFn ((Point.toProofString pt base).permutationCommonEvals) cr.2)))
        (pt ScalarSlot.beta) (pt ScalarSlot.gamma) (pt ScalarSlot.x) vk.delta vk.chunkLen
        (l0 pt) (lLast pt) (lBlind pt))
      (constraintValBudget vk) := by
  classical
  -- segment C: consecutive sets chain (case-free)
  have hC : ListRep vk (lagDen vk)
      (fun pt => (((List.ofFn fun s =>
          (Point.toProofString pt base).permutationSetEvals p s).drop 1).zip
          (List.ofFn fun s => (Point.toProofString pt base).permutationSetEvals p s)).map
        fun q => (q.1.eval - q.2.lastEval.getD 0) * l0 pt) (constraintValBudget vk) := by
    refine ListRep.ofMap (((List.finRange shape.numPermutationSets).drop 1).zip
        (List.finRange shape.numPermutationSets))
      (fun q pt => (pt (ScalarSlot.permEval p q.1)
        - ((Point.toProofString pt base).permutationSetEvals p q.2).lastEval.getD 0) * l0 pt)
      (fun q _ => ?_) (fun pt => ?_)
    · have h1 := (NumeratorRep.var (vk := vk) (ScalarSlot.permEval p q.1)).sub
        (lastEvalGetD_rep base p q.2)
      refine ((h1.mul h0).denCongr (one_mul _)).mono ?_
      simp only [constraintValBudget]
      omega
    · rw [List.ofFn_eq_map, ← List.map_drop, List.zip_map, List.map_map]
      rfl
  -- segment D: the chunk step rules (case-free)
  have hD : ListRep vk (lagDen vk)
      (fun pt => ((List.range (((List.ofFn fun s =>
          (Point.toProofString pt base).permutationSetEvals p s).zip
            vk.permutationChunks).map fun sc =>
          (sc.1, sc.2.map fun cr =>
            (cr.1.resolve (finFn ((Point.toProofString pt base).instanceEvals p))
              (finFn ((Point.toProofString pt base).adviceEvals p))
              (finFn ((Point.toProofString pt base).fixedEvals)),
            finFn ((Point.toProofString pt base).permutationCommonEvals) cr.2))).length).zip
          (((List.ofFn fun s =>
            (Point.toProofString pt base).permutationSetEvals p s).zip
              vk.permutationChunks).map fun sc =>
          (sc.1, sc.2.map fun cr =>
            (cr.1.resolve (finFn ((Point.toProofString pt base).instanceEvals p))
              (finFn ((Point.toProofString pt base).adviceEvals p))
              (finFn ((Point.toProofString pt base).fixedEvals)),
            finFn ((Point.toProofString pt base).permutationCommonEvals) cr.2)))).map
        fun q => permChunkExpression (pt ScalarSlot.beta) (pt ScalarSlot.gamma)
          (pt ScalarSlot.x) vk.delta vk.chunkLen q.1 q.2.1 q.2.2 (lLast pt) (lBlind pt))
      (constraintValBudget vk) := by
    have hMlen : ∀ pt : Point shape, (((List.ofFn fun s =>
        (Point.toProofString pt base).permutationSetEvals p s).zip
          vk.permutationChunks).map fun sc =>
        (sc.1, sc.2.map fun cr =>
          (cr.1.resolve (finFn ((Point.toProofString pt base).instanceEvals p))
            (finFn ((Point.toProofString pt base).adviceEvals p))
            (finFn ((Point.toProofString pt base).fixedEvals)),
          finFn ((Point.toProofString pt base).permutationCommonEvals) cr.2))).length
        = ((List.finRange shape.numPermutationSets).zip vk.permutationChunks).length := by
      intro pt
      rw [List.length_map, List.length_zip, List.length_ofFn, List.length_zip,
        List.length_finRange]
    refine ListRep.ofMap ((List.range
        ((List.finRange shape.numPermutationSets).zip vk.permutationChunks).length).zip
        ((List.finRange shape.numPermutationSets).zip vk.permutationChunks))
      (fun q pt => permChunkExpression (pt ScalarSlot.beta) (pt ScalarSlot.gamma)
        (pt ScalarSlot.x) vk.delta vk.chunkLen q.1
        ((Point.toProofString pt base).permutationSetEvals p q.2.1)
        (q.2.2.map fun cr =>
          (cr.1.resolve (finFn ((Point.toProofString pt base).instanceEvals p))
            (finFn ((Point.toProofString pt base).adviceEvals p))
            (finFn ((Point.toProofString pt base).fixedEvals)),
          finFn ((Point.toProofString pt base).permutationCommonEvals) cr.2))
        (lLast pt) (lBlind pt))
      (fun q hq => ?_) (fun pt => ?_)
    · have hmem : q.2.2 ∈ vk.permutationChunks :=
        (List.of_mem_zip (List.of_mem_zip hq).2).2
      have := permChunk_rep base p hL hB q.1 q.2.1 q.2.2 (hchunkW _ hmem)
      refine this.mono ?_
      simp only [constraintValBudget]
      omega
    · rw [hMlen pt, List.ofFn_eq_map, List.zip_map_left, List.map_map, List.zip_map_right,
        List.map_map]
      rfl
  by_cases hS : 0 < shape.numPermutationSets
  · -- both boundary rules are present; the matches reduce on `some`
    have hin : NumeratorRep vk 1 (fun pt => 1 - pt (ScalarSlot.permEval p ⟨0, hS⟩)) 1 := by
      simpa using (NumeratorRep.const (vk := vk) 1).sub
        (NumeratorRep.var (ScalarSlot.permEval p ⟨0, hS⟩))
    have hrepA : NumeratorRep vk (lagDen vk)
        (fun pt => l0 pt * (1 - pt (ScalarSlot.permEval p ⟨0, hS⟩)))
        (constraintValBudget vk) := by
      refine ((h0.mul hin).denCongr (mul_one _)).mono ?_
      simp only [constraintValBudget]
      omega
    have hsq : NumeratorRep vk 1
        (fun pt => pt (ScalarSlot.permEval p ⟨shape.numPermutationSets - 1, by omega⟩) ^ 2
          - pt (ScalarSlot.permEval p ⟨shape.numPermutationSets - 1, by omega⟩)) 2 := by
      have hp := ((NumeratorRep.var (vk := vk)
        (ScalarSlot.permEval p ⟨shape.numPermutationSets - 1, by omega⟩)).pow 2).denCongr
        (one_pow 2)
      simpa using (hp.sub (NumeratorRep.var
        (ScalarSlot.permEval p ⟨shape.numPermutationSets - 1, by omega⟩))).mono (by omega)
    have hrepB : NumeratorRep vk (lagDen vk)
        (fun pt => (pt (ScalarSlot.permEval p ⟨shape.numPermutationSets - 1, by omega⟩) ^ 2
          - pt (ScalarSlot.permEval p ⟨shape.numPermutationSets - 1, by omega⟩)) * lLast pt)
        (constraintValBudget vk) := by
      refine ((hsq.mul hL).denCongr (one_mul _)).mono ?_
      simp only [constraintValBudget]
      omega
    refine ListRep.congr (fun pt => ?_)
      ((((ListRep.singleton hrepA).append (ListRep.singleton hrepB)).append hC).append hD)
    unfold permutationExpressions
    rw [head?_ofFn _ hS, getLast?_ofFn _ hS]
    rfl
  · -- no permutation sets: every segment is empty
    have hS0 : shape.numPermutationSets = 0 := by omega
    refine ListRep.congr (fun pt => ?_) (ListRep.nil (vk := vk))
    have hnil : (List.ofFn fun s =>
        (Point.toProofString pt base).permutationSetEvals p s) = [] := by
      have := List.length_ofFn (f := fun s =>
        (Point.toProofString pt base).permutationSetEvals p s)
      exact List.eq_nil_of_length_eq_zero (by omega)
    unfold permutationExpressions
    rw [hnil]
    rfl

/-- Every lookup input/table expression's degree bound is under `lookupExprBudget`. -/
theorem lookup_expr_degree_le (l : Fin shape.numLookups) :
    (∀ e ∈ vk.lookupInputExprs l, e.degreeBound ≤ lookupExprBudget vk)
      ∧ ∀ e ∈ vk.lookupTableExprs l, e.degreeBound ≤ lookupExprBudget vk := by
  constructor
  · intro e he
    refine le_trans (le_foldr_max (List.mem_map.mpr ⟨e, he, rfl⟩)) ?_
    exact le_trans (le_max_left _ _) (le_foldr_max (List.mem_ofFn.mpr ⟨l, rfl⟩))
  · intro e he
    refine le_trans (le_foldr_max (List.mem_map.mpr ⟨e, he, rfl⟩)) ?_
    exact le_trans (le_max_right _ _) (le_foldr_max (List.mem_ofFn.mpr ⟨l, rfl⟩))

/-- Every lookup input/table expression list's length is under `lookupLenBudget`. -/
theorem lookup_expr_length_le (l : Fin shape.numLookups) :
    (vk.lookupInputExprs l).length ≤ lookupLenBudget vk
      ∧ (vk.lookupTableExprs l).length ≤ lookupLenBudget vk :=
  ⟨le_trans (le_max_left _ _) (le_foldr_max (List.mem_ofFn.mpr ⟨l, rfl⟩)),
    le_trans (le_max_right _ _) (le_foldr_max (List.mem_ofFn.mpr ⟨l, rfl⟩))⟩

/-- A `θ`-compressed expression list, represented over the trivial denominator at the lookup
compression budget. -/
theorem compress_rep (base : ProofString shape Fp G) (p : Fin shape.numProofs)
    (exprs : List (Expr Fp))
    (hd : ∀ e ∈ exprs, e.degreeBound ≤ lookupExprBudget vk)
    (hlen : exprs.length ≤ lookupLenBudget vk) :
    NumeratorRep vk 1
      (fun pt => compressExprs (finFn ((Point.toProofString pt base).fixedEvals))
        (finFn ((Point.toProofString pt base).adviceEvals p))
        (finFn ((Point.toProofString pt base).instanceEvals p))
        (pt ScalarSlot.theta) exprs)
      (lookupExprBudget vk + lookupLenBudget vk) := by
  obtain ⟨hf, ha, hi⟩ := finFn_feeds_rep (vk := vk) base p
  have hfold := NumeratorRep.foldl_scale_add (vk := vk) (den := 1) ScalarSlot.theta
    (exprs.map fun e pt => e.eval (finFn ((Point.toProofString pt base).fixedEvals))
      (finFn ((Point.toProofString pt base).adviceEvals p))
      (finFn ((Point.toProofString pt base).instanceEvals p)))
    (fun f hf' => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hf'
      exact (NumeratorRep.exprEval hf ha hi e).mono (hd e he))
  refine (hfold.mono ?_).congr_event fun pt _ => ?_
  · rw [List.length_map]
    omega
  · show ((exprs.map _).map _).foldl _ 0 = _
    rw [List.map_map, List.foldl_map]
    rfl

section LookupSegment

variable (base : ProofString shape Fp G) (p : Fin shape.numProofs)
variable {l0 lLast lBlind : Point shape → Fp}

/-- One lookup's five constraint rules, represented over `lagDen`, in the exact spelling
`subProofExpressions` produces. -/
theorem lookupBlock_listRep (l : Fin shape.numLookups)
    (h0 : NumeratorRep vk (lagDen vk) l0 (lagBudget vk))
    (hL : NumeratorRep vk (lagDen vk) lLast (lagBudget vk))
    (hB : NumeratorRep vk (lagDen vk) lBlind (lagBudget vk)) :
    ListRep vk (lagDen vk)
      (fun pt => lookupExpressions ((Point.toProofString pt base).lookupEvals p l)
        (vk.lookupInputExprs l) (vk.lookupTableExprs l)
        (finFn ((Point.toProofString pt base).fixedEvals))
        (finFn ((Point.toProofString pt base).adviceEvals p))
        (finFn ((Point.toProofString pt base).instanceEvals p))
        (pt ScalarSlot.theta) (pt ScalarSlot.beta) (pt ScalarSlot.gamma)
        (l0 pt) (lLast pt) (lBlind pt))
      (constraintValBudget vk) := by
  have hcin := compress_rep base p (vk.lookupInputExprs l)
    (lookup_expr_degree_le l).1 (lookup_expr_length_le l).1
  have hct := compress_rep base p (vk.lookupTableExprs l)
    (lookup_expr_degree_le l).2 (lookup_expr_length_le l).2
  have hactive := activeRow_rep (vk := vk) hL hB
  -- the five rules
  have he1 : NumeratorRep vk (lagDen vk)
      (fun pt => l0 pt * (1 - pt (ScalarSlot.lookupProductEval p l)))
      (constraintValBudget vk) := by
    have hin : NumeratorRep vk 1 (fun pt => 1 - pt (ScalarSlot.lookupProductEval p l)) 1 := by
      simpa using (NumeratorRep.const (vk := vk) 1).sub
        (NumeratorRep.var (ScalarSlot.lookupProductEval p l))
    refine ((h0.mul hin).denCongr (mul_one _)).mono ?_
    simp only [constraintValBudget]
    omega
  have he2 : NumeratorRep vk (lagDen vk)
      (fun pt => lLast pt * (pt (ScalarSlot.lookupProductEval p l) ^ 2
        - pt (ScalarSlot.lookupProductEval p l)))
      (constraintValBudget vk) := by
    have hsq : NumeratorRep vk 1 (fun pt => pt (ScalarSlot.lookupProductEval p l) ^ 2
        - pt (ScalarSlot.lookupProductEval p l)) 2 := by
      have hp := ((NumeratorRep.var (vk := vk) (ScalarSlot.lookupProductEval p l)).pow 2).denCongr
        (one_pow 2)
      simpa using (hp.sub (NumeratorRep.var (ScalarSlot.lookupProductEval p l))).mono (by omega)
    refine ((hL.mul hsq).denCongr (mul_one _)).mono ?_
    simp only [constraintValBudget]
    omega
  have he3 : NumeratorRep vk (lagDen vk)
      (fun pt => (pt (ScalarSlot.lookupProductNextEval p l)
          * (pt (ScalarSlot.lookupPermInputEval p l) + pt ScalarSlot.beta)
          * (pt (ScalarSlot.lookupPermTableEval p l) + pt ScalarSlot.gamma)
        - pt (ScalarSlot.lookupProductEval p l)
          * (compressExprs (finFn ((Point.toProofString pt base).fixedEvals))
              (finFn ((Point.toProofString pt base).adviceEvals p))
              (finFn ((Point.toProofString pt base).instanceEvals p))
              (pt ScalarSlot.theta) (vk.lookupInputExprs l) + pt ScalarSlot.beta)
          * (compressExprs (finFn ((Point.toProofString pt base).fixedEvals))
              (finFn ((Point.toProofString pt base).adviceEvals p))
              (finFn ((Point.toProofString pt base).instanceEvals p))
              (pt ScalarSlot.theta) (vk.lookupTableExprs l) + pt ScalarSlot.gamma))
        * (1 - (lLast pt + lBlind pt)))
      (constraintValBudget vk) := by
    have hleft : NumeratorRep vk 1
        (fun pt => pt (ScalarSlot.lookupProductNextEval p l)
          * (pt (ScalarSlot.lookupPermInputEval p l) + pt ScalarSlot.beta)
          * (pt (ScalarSlot.lookupPermTableEval p l) + pt ScalarSlot.gamma)) 3 := by
      have h1 := (NumeratorRep.var (vk := vk) (ScalarSlot.lookupPermInputEval p l)).add
        (NumeratorRep.var ScalarSlot.beta)
      have h2 := (NumeratorRep.var (vk := vk) (ScalarSlot.lookupPermTableEval p l)).add
        (NumeratorRep.var ScalarSlot.gamma)
      have h3 := ((NumeratorRep.var (vk := vk)
        (ScalarSlot.lookupProductNextEval p l)).mul h1).denCongr (one_mul 1)
      have h4 := (h3.mul h2).denCongr (one_mul 1)
      exact h4.mono (by omega)
    have hright : NumeratorRep vk 1
        (fun pt => pt (ScalarSlot.lookupProductEval p l)
          * (compressExprs (finFn ((Point.toProofString pt base).fixedEvals))
              (finFn ((Point.toProofString pt base).adviceEvals p))
              (finFn ((Point.toProofString pt base).instanceEvals p))
              (pt ScalarSlot.theta) (vk.lookupInputExprs l) + pt ScalarSlot.beta)
          * (compressExprs (finFn ((Point.toProofString pt base).fixedEvals))
              (finFn ((Point.toProofString pt base).adviceEvals p))
              (finFn ((Point.toProofString pt base).instanceEvals p))
              (pt ScalarSlot.theta) (vk.lookupTableExprs l) + pt ScalarSlot.gamma))
        (1 + 2 * (lookupExprBudget vk + lookupLenBudget vk + 1)) := by
      have h1 := hcin.add (NumeratorRep.var ScalarSlot.beta)
      have h2 := hct.add (NumeratorRep.var ScalarSlot.gamma)
      have h3 := ((NumeratorRep.var (vk := vk)
        (ScalarSlot.lookupProductEval p l)).mul h1).denCongr (one_mul 1)
      have h4 := (h3.mul h2).denCongr (one_mul 1)
      exact h4.mono (by omega)
    have hdiff := hleft.sub hright
    refine ((hdiff.mul hactive).denCongr (one_mul _)).mono ?_
    simp only [constraintValBudget]
    omega
  have he4 : NumeratorRep vk (lagDen vk)
      (fun pt => l0 pt * (pt (ScalarSlot.lookupPermInputEval p l)
        - pt (ScalarSlot.lookupPermTableEval p l)))
      (constraintValBudget vk) := by
    have hin : NumeratorRep vk 1 (fun pt => pt (ScalarSlot.lookupPermInputEval p l)
        - pt (ScalarSlot.lookupPermTableEval p l)) 1 := by
      simpa using (NumeratorRep.var (vk := vk) (ScalarSlot.lookupPermInputEval p l)).sub
        (NumeratorRep.var (ScalarSlot.lookupPermTableEval p l))
    refine ((h0.mul hin).denCongr (mul_one _)).mono ?_
    simp only [constraintValBudget]
    omega
  have he5 : NumeratorRep vk (lagDen vk)
      (fun pt => (pt (ScalarSlot.lookupPermInputEval p l)
          - pt (ScalarSlot.lookupPermTableEval p l))
        * (pt (ScalarSlot.lookupPermInputEval p l)
          - pt (ScalarSlot.lookupPermInputInvEval p l))
        * (1 - (lLast pt + lBlind pt)))
      (constraintValBudget vk) := by
    have h1 : NumeratorRep vk 1 (fun pt => pt (ScalarSlot.lookupPermInputEval p l)
        - pt (ScalarSlot.lookupPermTableEval p l)) 1 := by
      simpa using (NumeratorRep.var (vk := vk) (ScalarSlot.lookupPermInputEval p l)).sub
        (NumeratorRep.var (ScalarSlot.lookupPermTableEval p l))
    have h2 : NumeratorRep vk 1 (fun pt => pt (ScalarSlot.lookupPermInputEval p l)
        - pt (ScalarSlot.lookupPermInputInvEval p l)) 1 := by
      simpa using (NumeratorRep.var (vk := vk) (ScalarSlot.lookupPermInputEval p l)).sub
        (NumeratorRep.var (ScalarSlot.lookupPermInputInvEval p l))
    have h3 := ((h1.mul h2).denCongr (one_mul 1)).mono (a := 1 + 1) (b := 2) le_rfl
    refine ((h3.mul hactive).denCongr (one_mul _)).mono ?_
    simp only [constraintValBudget]
    omega
  exact ⟨[_, _, _, _, _], fun pt => rfl,
    by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl
      exacts [he1, he2, he3, he4, he5]⟩

/-- The lookup segment of a sub-proof's constraint list, represented over `lagDen`. -/
theorem lookupSeg_listRep
    (h0 : NumeratorRep vk (lagDen vk) l0 (lagBudget vk))
    (hL : NumeratorRep vk (lagDen vk) lLast (lagBudget vk))
    (hB : NumeratorRep vk (lagDen vk) lBlind (lagBudget vk)) :
    ListRep vk (lagDen vk)
      (fun pt => (List.ofFn fun l => lookupExpressions
        ((Point.toProofString pt base).lookupEvals p l) (vk.lookupInputExprs l)
        (vk.lookupTableExprs l) (finFn ((Point.toProofString pt base).fixedEvals))
        (finFn ((Point.toProofString pt base).adviceEvals p))
        (finFn ((Point.toProofString pt base).instanceEvals p))
        (pt ScalarSlot.theta) (pt ScalarSlot.beta) (pt ScalarSlot.gamma)
        (l0 pt) (lLast pt) (lBlind pt)).flatten)
      (constraintValBudget vk) := by
  refine ListRep.congr (fun pt => ?_)
    (ListRep.flattenMap (List.finRange shape.numLookups) _
      (fun l _ => lookupBlock_listRep base p l h0 hL hB))
  rw [List.ofFn_eq_map]

end LookupSegment

section SubProof

variable (base : ProofString shape Fp G)
variable {l0 lLast lBlind : Point shape → Fp}

/-- One sub-proof's whole constraint list, represented over `lagDen`. -/
theorem subProofExpressions_listRep
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (h0 : NumeratorRep vk (lagDen vk) l0 (lagBudget vk))
    (hL : NumeratorRep vk (lagDen vk) lLast (lagBudget vk))
    (hB : NumeratorRep vk (lagDen vk) lBlind (lagBudget vk)) (p : Fin shape.numProofs) :
    ListRep vk (lagDen vk)
      (fun pt => subProofExpressions vk (Point.toProofString pt base) (Point.toChallenges pt)
        (l0 pt) (lLast pt) (lBlind pt) p)
      (constraintValBudget vk) := by
  have hgates := gateSeg_listRep (vk := vk) base p
  have hperm := permSeg_listRep base p hchunkW h0 hL hB
  have hlkp := lookupSeg_listRep base p h0 hL hB
  refine ListRep.congr (fun pt => ?_) ((hgates.append hperm).append hlkp)
  rfl

/-- The whole constraint list across the sub-proofs, represented over `lagDen`. -/
theorem allExpressions_listRep
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (h0 : NumeratorRep vk (lagDen vk) l0 (lagBudget vk))
    (hL : NumeratorRep vk (lagDen vk) lLast (lagBudget vk))
    (hB : NumeratorRep vk (lagDen vk) lBlind (lagBudget vk)) :
    ListRep vk (lagDen vk)
      (fun pt => allExpressions vk (Point.toProofString pt base) (Point.toChallenges pt)
        (l0 pt) (lLast pt) (lBlind pt))
      (constraintValBudget vk) := by
  refine ListRep.congr (fun pt => ?_)
    (ListRep.flattenMap (List.finRange shape.numProofs) _
      (fun p _ => subProofExpressions_listRep base hchunkW h0 hL hB p))
  show _ = (List.ofFn _).flatten
  rw [List.ofFn_eq_map]

end SubProof

end PermSegment

/-! ## The constraint-list length and Stage 4: `expectedHEval` -/

/-- The length of one lookup rule block is five. -/
theorem lookupExpressions_length {F : Type*} [CommRing F] (le : LookupEval F)
    (inputExprs tableExprs : List (Expr F)) (fixedEvals adviceEvals instanceEvals : ℕ → F)
    (theta beta gamma l0 lLast lBlind : F) :
    (lookupExpressions le inputExprs tableExprs fixedEvals adviceEvals instanceEvals
      theta beta gamma l0 lLast lBlind).length = 5 := rfl

/-- The exact length of `allExpressions` for any inputs: the boundary rules exist when there is
at least one permutation set, and the chunk layout has one entry per set. -/
theorem allExpressions_length {G' : Type*}
    (vk' : VerifyingKey shape Fp G') (ps : ProofString shape Fp G')
    (ch : Challenges shape.k Fp) (l0 lLast lBlind : Fp)
    (hchunks : vk'.permutationChunks.length = shape.numPermutationSets)
    (hS : 1 ≤ shape.numPermutationSets) :
    (allExpressions vk' ps ch l0 lLast lBlind).length = constraintBudget shape vk' := by
  have hsub : ∀ p : Fin shape.numProofs,
      (subProofExpressions vk' ps ch l0 lLast lBlind p).length
        = vk'.gates.length + (2 * shape.numPermutationSets + 1) + 5 * shape.numLookups := by
    intro p
    show (_ ++ permutationExpressions _ _ _ _ _ _ _ _ _ _ ++ _).length = _
    rw [List.length_append, List.length_append]
    have hgates : (vk'.gates.map fun g => g.eval (finFn ps.fixedEvals)
        (finFn (ps.adviceEvals p)) (finFn (ps.instanceEvals p))).length
        = vk'.gates.length := List.length_map ..
    have hperm : (permutationExpressions
        (List.ofFn fun s => ps.permutationSetEvals p s)
        (((List.ofFn fun s => ps.permutationSetEvals p s).zip vk'.permutationChunks).map
          fun sc => (sc.1, sc.2.map fun cr =>
            (cr.1.resolve (finFn (ps.instanceEvals p)) (finFn (ps.adviceEvals p))
              (finFn ps.fixedEvals), finFn ps.permutationCommonEvals cr.2)))
        ch.beta ch.gamma ch.x vk'.delta vk'.chunkLen l0 lLast lBlind).length
        = 2 * shape.numPermutationSets + 1 := by
      unfold permutationExpressions
      rw [head?_ofFn _ (by omega), getLast?_ofFn _ (by omega)]
      simp only [List.length_append, List.length_map, List.length_zip, List.length_drop,
        List.length_ofFn, List.length_range, List.length_cons, List.length_nil, hchunks]
      omega
    have hlkp : ((List.ofFn fun l => lookupExpressions (ps.lookupEvals p l)
        (vk'.lookupInputExprs l) (vk'.lookupTableExprs l) (finFn ps.fixedEvals)
        (finFn (ps.adviceEvals p)) (finFn (ps.instanceEvals p)) ch.theta ch.beta ch.gamma
        l0 lLast lBlind).flatten).length = 5 * shape.numLookups := by
      rw [List.length_flatten, List.map_ofFn]
      have : ∀ l : Fin shape.numLookups,
          (List.length ∘ fun l => lookupExpressions (ps.lookupEvals p l)
            (vk'.lookupInputExprs l) (vk'.lookupTableExprs l) (finFn ps.fixedEvals)
            (finFn (ps.adviceEvals p)) (finFn (ps.instanceEvals p)) ch.theta ch.beta ch.gamma
            l0 lLast lBlind) l = 5 := fun l => rfl
      calc (List.ofFn (List.length ∘ fun l => lookupExpressions (ps.lookupEvals p l)
            (vk'.lookupInputExprs l) (vk'.lookupTableExprs l) (finFn ps.fixedEvals)
            (finFn (ps.adviceEvals p)) (finFn (ps.instanceEvals p)) ch.theta ch.beta ch.gamma
            l0 lLast lBlind)).sum
          = (List.ofFn fun _ : Fin shape.numLookups => 5).sum := by
            refine congrArg List.sum ?_
            exact congrArg List.ofFn (funext this)
        _ = 5 * shape.numLookups := by
            rw [List.ofFn_const, List.sum_replicate, smul_eq_mul]
            omega
    rw [hgates, hperm, hlkp]
  show ((List.ofFn fun p => subProofExpressions vk' ps ch l0 lLast lBlind p).flatten).length = _
  rw [List.length_flatten, List.map_ofFn]
  calc (List.ofFn (List.length ∘ fun p => subProofExpressions vk' ps ch l0 lLast lBlind p)).sum
      = (List.ofFn fun _ : Fin shape.numProofs => vk'.gates.length
          + (2 * shape.numPermutationSets + 1) + 5 * shape.numLookups).sum := by
        refine congrArg List.sum (congrArg List.ofFn (funext fun p => ?_))
        exact hsub p
    _ = constraintBudget shape vk' := by
        rw [List.ofFn_const, List.sum_replicate, smul_eq_mul, constraintBudget]

section StageFour

variable (base : ProofString shape Fp G)

/-- **Stage 4.** The vanishing argument's `expected_h_eval`, exactly as `assembleQueries`
computes it — the `y`-fold of the constraint list at the Lagrange basis values, divided by
`xⁿ − 1` — represented over `vanDen` at `hEvalBudget`. -/
theorem expectedHEval_rep
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (hchunks : vk.permutationChunks.length = shape.numPermutationSets)
    (hS : 1 ≤ shape.numPermutationSets) :
    NumeratorRep vk (vanDen vk)
      (fun pt => expectedHEval
        (allExpressions vk (Point.toProofString pt base) (Point.toChallenges pt)
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
            (pt ScalarSlot.x)).1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
            (pt ScalarSlot.x)).2.1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
            (pt ScalarSlot.x)).2.2)
        (pt ScalarSlot.y) (pt ScalarSlot.x ^ vk.n))
      (hEvalBudget shape vk) := by
  obtain ⟨fns, heq, hrep⟩ := allExpressions_listRep base hchunkW
    (lagrangeBasis_l0_rep (vk := vk)) (lagrangeBasis_lLast_rep (vk := vk))
    (lagrangeBasis_lBlind_rep (vk := vk))
  have hlen : fns.length = constraintBudget shape vk := by
    set pt0 : Point shape := fun _ => 0 with hpt0
    have h0 := heq pt0
    beta_reduce at h0
    have hAE := allExpressions_length vk (Point.toProofString pt0 base)
      (Point.toChallenges pt0)
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt0 ScalarSlot.x ^ vk.n)
        (pt0 ScalarSlot.x)).1
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt0 ScalarSlot.x ^ vk.n)
        (pt0 ScalarSlot.x)).2.1
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt0 ScalarSlot.x ^ vk.n)
        (pt0 ScalarSlot.x)).2.2 hchunks hS
    rw [h0, List.length_map] at hAE
    exact hAE
  have hfold := NumeratorRep.foldl_scale_add (vk := vk) (den := lagDen vk) ScalarSlot.y fns hrep
  have hfold' : NumeratorRep vk (lagDen vk)
      (fun pt => ((allExpressions vk (Point.toProofString pt base) (Point.toChallenges pt)
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
            (pt ScalarSlot.x)).1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
            (pt ScalarSlot.x)).2.1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (pt ScalarSlot.x ^ vk.n)
            (pt ScalarSlot.x)).2.2)).foldl
        (fun acc v => acc * pt ScalarSlot.y + v) 0)
      (constraintValBudget vk + (constraintBudget shape vk - 1)) := by
    rw [← hlen]
    exact hfold.congr_event fun pt _ =>
      congrArg (fun l => l.foldl (fun acc v => acc * pt ScalarSlot.y + v) 0) (heq pt).symm
  have hxn : (X ScalarSlot.x ^ vk.n - 1 : MvPolynomial (ScalarSlot shape) Fp)
      ∈ denFactors vk := by
    simp [denFactors]
  have hdiv := hfold'.divFactor _ hxn
  refine (hdiv.mono ?_).congr_event fun pt hpt => ?_
  · simp only [hEvalBudget]
    omega
  · show _ = expectedHEval _ _ _
    rw [expectedHEval]
    have : eval pt (X ScalarSlot.x ^ vk.n - 1 : MvPolynomial (ScalarSlot shape) Fp)
        = pt ScalarSlot.x ^ vk.n - 1 := by simp
    rw [this]

end StageFour

end Zcash.Snark
