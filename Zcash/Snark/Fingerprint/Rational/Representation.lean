import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Fingerprint.Rational.GoodEvent

/-!
# Rational representations on the good event

The representation walk's carrier predicate. A pipeline value — a function of the sample point —
is *represented* by a polynomial numerator over an explicit denominator when the cleared
identity `f pt · den(pt) = num(pt)` holds at every good point:

* `NumeratorRep vk den f dNum` — existential numerator of total degree ≤ `dNum` over the
  **explicit** denominator `den`. Keeping `den` explicit is what lets same-denominator sums and
  the `y`/`x₁`/`x₂`/`x₄` folds combine without denominator inflation.
* `RationalRep vk f dNum dDen` — the packaged form: some numerator/denominator pair with the
  denominator a product of enumerated factors (`Submonoid.closure` of `denFactors`), which is
  what makes `den(pt) ≠ 0` on the event definitional (`den_eval_ne_zero`) and the cleared
  identity mean agreement.

The toolkit below closes `NumeratorRep` under the pipeline's combinators. The two lemmas that
consume the good event are `divFactor`/`invFactor` — every other step is pure algebra under
`MvPolynomial.eval`. `foldl_scale_add` is the challenge-fold rule: unlike the committed-world
degree walk (`Soundness/DegreeWalk.lean`), where `y`/`θ` are `C`-scalars and folds preserve
degree, here the fold variable is a sample-space coordinate and each step costs one degree unit.
-/

namespace Zcash.Snark

open MvPolynomial

/-- `f` agrees with `num / den` on the good event, for an explicit `den` and some numerator of
total degree ≤ `dNum` — stated in cleared form, so no division appears. -/
def NumeratorRep {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G)
    (den : MvPolynomial (ScalarSlot shape) Fp) (f : Point shape → Fp) (dNum : ℕ) : Prop :=
  ∃ num : MvPolynomial (ScalarSlot shape) Fp, num.totalDegree ≤ dNum ∧
    ∀ pt : Point shape, GoodEvent vk pt → f pt * eval pt den = eval pt num

/-- The packaged rational representation: some numerator and some product of enumerated
denominator factors, with total-degree bounds on both. The factor-closure membership is what
turns the cleared identity into agreement on the event (`den_eval_ne_zero`). Destructure as
`⟨num, den, den_mem, hNum, hDen, agrees⟩`. -/
def RationalRep {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G)
    (f : Point shape → Fp) (dNum dDen : ℕ) : Prop :=
  ∃ num den : MvPolynomial (ScalarSlot shape) Fp,
    den ∈ Submonoid.closure {φ | φ ∈ denFactors vk}
      ∧ num.totalDegree ≤ dNum ∧ den.totalDegree ≤ dDen
      ∧ ∀ pt : Point shape, GoodEvent vk pt → f pt * eval pt den = eval pt num

namespace NumeratorRep

variable {shape : Shape} {G : Type*} {vk : VerifyingKey shape Fp G}
variable {den den₁ den₂ : MvPolynomial (ScalarSlot shape) Fp}
variable {f g : Point shape → Fp} {a b : ℕ}

/-- Weaken the degree bound. -/
theorem mono (hab : a ≤ b) (h : NumeratorRep vk den f a) : NumeratorRep vk den f b :=
  let ⟨num, hd, hagree⟩ := h
  ⟨num, hd.trans hab, hagree⟩

/-- Replace the represented function by one agreeing with it on the event — the rewrite rule
along grouping stability. -/
theorem congr_event (hfg : ∀ pt : Point shape, GoodEvent vk pt → f pt = g pt)
    (h : NumeratorRep vk den f a) : NumeratorRep vk den g a :=
  let ⟨num, hd, hagree⟩ := h
  ⟨num, hd, fun pt hpt => by rw [← hfg pt hpt]; exact hagree pt hpt⟩

/-- A polynomial's evaluation represents itself over the trivial denominator. -/
theorem ofPoly (p : MvPolynomial (ScalarSlot shape) Fp) :
    NumeratorRep vk 1 (fun pt => eval pt p) p.totalDegree :=
  ⟨p, le_rfl, fun pt _ => by simp⟩

/-- A constant, over the trivial denominator. -/
theorem const (c : Fp) : NumeratorRep vk 1 (fun _ => c) 0 :=
  ⟨C c, by simp [totalDegree_C], fun pt _ => by simp⟩

/-- A sample-space coordinate, over the trivial denominator. -/
theorem var (v : ScalarSlot shape) : NumeratorRep vk 1 (fun pt => pt v) 1 :=
  ⟨X v, by simp [totalDegree_X], fun pt _ => by simp⟩

/-- Same-denominator sum: numerators add, degrees max — no denominator inflation. -/
theorem add (hf : NumeratorRep vk den f a) (hg : NumeratorRep vk den g b) :
    NumeratorRep vk den (fun pt => f pt + g pt) (max a b) := by
  obtain ⟨nf, hdf, haf⟩ := hf
  obtain ⟨ng, hdg, hag⟩ := hg
  refine ⟨nf + ng, le_trans (totalDegree_add nf ng) (max_le_max hdf hdg), fun pt hpt => ?_⟩
  rw [map_add, ← haf pt hpt, ← hag pt hpt, add_mul]

/-- Negation preserves the degree bound. -/
theorem neg (hf : NumeratorRep vk den f a) : NumeratorRep vk den (fun pt => -f pt) a := by
  obtain ⟨nf, hdf, haf⟩ := hf
  refine ⟨-nf, by simpa using hdf, fun pt hpt => ?_⟩
  rw [map_neg, ← haf pt hpt, neg_mul]

/-- Same-denominator difference. -/
theorem sub (hf : NumeratorRep vk den f a) (hg : NumeratorRep vk den g b) :
    NumeratorRep vk den (fun pt => f pt - g pt) (max a b) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- Scaling by a constant preserves the degree bound. -/
theorem smul (c : Fp) (hf : NumeratorRep vk den f a) :
    NumeratorRep vk den (fun pt => c * f pt) a := by
  obtain ⟨nf, hdf, haf⟩ := hf
  refine ⟨C c * nf, le_trans (totalDegree_mul _ _) (by simpa [totalDegree_C] using hdf),
    fun pt hpt => ?_⟩
  rw [map_mul, eval_C, ← haf pt hpt, mul_assoc]

/-- Product: denominators multiply, degrees add. -/
theorem mul (hf : NumeratorRep vk den₁ f a) (hg : NumeratorRep vk den₂ g b) :
    NumeratorRep vk (den₁ * den₂) (fun pt => f pt * g pt) (a + b) := by
  obtain ⟨nf, hdf, haf⟩ := hf
  obtain ⟨ng, hdg, hag⟩ := hg
  refine ⟨nf * ng, le_trans (totalDegree_mul _ _) (Nat.add_le_add hdf hdg), fun pt hpt => ?_⟩
  rw [map_mul, map_mul, ← haf pt hpt, ← hag pt hpt]
  ring

/-- Power: iterated `mul`. -/
theorem pow (m : ℕ) (hf : NumeratorRep vk den f a) :
    NumeratorRep vk (den ^ m) (fun pt => f pt ^ m) (m * a) := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.zero_mul]
    exact ⟨1, by simp, fun pt _ => by simp⟩
  | succ m ih =>
    have h := ih.mul hf
    simp only [pow_succ, Nat.succ_mul]
    exact h

/-- Weaken along a denominator extension: multiplying the denominator multiplies the numerator,
with no event hypothesis — the cleared identity is pure algebra. -/
theorem extend (d' : MvPolynomial (ScalarSlot shape) Fp)
    (hf : NumeratorRep vk den f a) : NumeratorRep vk (den * d') f (a + d'.totalDegree) := by
  obtain ⟨nf, hdf, haf⟩ := hf
  refine ⟨nf * d', le_trans (totalDegree_mul _ _) (Nat.add_le_add hdf le_rfl),
    fun pt hpt => ?_⟩
  rw [map_mul, map_mul, ← haf pt hpt]
  ring

/-- Dividing by an enumerated factor moves it into the denominator — one of the two toolkit
steps that consume the good event. -/
theorem divFactor (φ : MvPolynomial (ScalarSlot shape) Fp) (hφ : φ ∈ denFactors vk)
    (hf : NumeratorRep vk den f a) :
    NumeratorRep vk (den * φ) (fun pt => f pt * (eval pt φ)⁻¹) a := by
  obtain ⟨nf, hdf, haf⟩ := hf
  refine ⟨nf, hdf, fun pt hpt => ?_⟩
  have hφne : eval pt φ ≠ 0 := hpt φ hφ
  rw [map_mul, ← haf pt hpt]
  field_simp

/-- The inverse of an enumerated factor is represented by `1` over that factor. -/
theorem invFactor (φ : MvPolynomial (ScalarSlot shape) Fp) (hφ : φ ∈ denFactors vk) :
    NumeratorRep vk φ (fun pt => (eval pt φ)⁻¹) 0 := by
  refine ⟨1, by simp, fun pt hpt => ?_⟩
  have hφne : eval pt φ ≠ 0 := hpt φ hφ
  simp [inv_mul_cancel₀ hφne]

/-- A same-denominator list sum. -/
theorem listSum (l : List (Point shape → Fp))
    (h : ∀ f ∈ l, NumeratorRep vk den f a) :
    NumeratorRep vk den (fun pt => (l.map (· pt)).sum) a := by
  induction l with
  | nil => exact ⟨0, by simp, fun pt _ => by simp⟩
  | cons f t ih =>
    have hf := h f List.mem_cons_self
    have ht := ih fun g hg => h g (List.mem_cons_of_mem _ hg)
    simpa using (hf.add ht).mono (by omega)

/-- The challenge-fold rule, accumulator-generalized: folding `acc ↦ acc · pt s + v` over a list
whose elements are represented at degree ≤ `a`, starting from an accumulator represented at
degree ≤ `b`, is represented at degree ≤ `max (b + length) (a + (length − 1))` — each step costs
one degree unit, because the fold variable is a coordinate, not a scalar (contrast
`natDegree_foldByY_le`, the committed-world fold, which preserves degree). -/
theorem foldl_scale_add_aux (s : ScalarSlot shape) (l : List (Point shape → Fp))
    (h : ∀ f ∈ l, NumeratorRep vk den f a) :
    ∀ (acc : Point shape → Fp) (b : ℕ), NumeratorRep vk den acc b →
      NumeratorRep vk den
        (fun pt => (l.map (· pt)).foldl (fun acc' v => acc' * pt s + v) (acc pt))
        (max (b + l.length) (a + (l.length - 1))) := by
  induction l with
  | nil =>
    intro acc b hacc
    simp only [List.map_nil, List.foldl_nil, List.length_nil, Nat.add_zero, Nat.zero_sub]
    exact hacc.mono (le_max_left b a)
  | cons f t ih =>
    intro acc b hacc
    have hmul : NumeratorRep vk den (fun pt => acc pt * pt s) (b + 1) := by
      have h1 := hacc.mul (var (vk := vk) s)
      rw [mul_one] at h1
      exact h1
    have hstep : NumeratorRep vk den (fun pt => acc pt * pt s + f pt) (max (b + 1) a) :=
      hmul.add (h f List.mem_cons_self)
    have ht := ih (fun g hg => h g (List.mem_cons_of_mem _ hg)) _ _ hstep
    exact ht.mono (by simp only [List.length_cons]; omega)

/-- The challenge-fold rule from a zero accumulator — the shape of the verifier's
`y`/`x₁`/`x₂`/`x₄` folds: elements at degree ≤ `a` fold to degree ≤ `a + (length − 1)`. -/
theorem foldl_scale_add (s : ScalarSlot shape) (l : List (Point shape → Fp))
    (h : ∀ f ∈ l, NumeratorRep vk den f a) :
    NumeratorRep vk den
      (fun pt => (l.map (· pt)).foldl (fun acc' v => acc' * pt s + v) 0)
      (a + (l.length - 1)) := by
  cases l with
  | nil => exact ⟨0, by simp, fun pt _ => by simp⟩
  | cons f t =>
    have hf : NumeratorRep vk den (fun pt => 0 * pt s + f pt) a :=
      (h f List.mem_cons_self).congr_event fun pt _ => by ring
    have haux := foldl_scale_add_aux s t (fun g hg => h g (List.mem_cons_of_mem _ hg))
      (fun pt => 0 * pt s + f pt) a hf
    exact haux.mono (by simp only [List.length_cons]; omega)

/-- Package a walked representation, once the denominator is placed in the factor closure. -/
theorem toRational {dDen : ℕ} (hmem : den ∈ Submonoid.closure {φ | φ ∈ denFactors vk})
    (hden : den.totalDegree ≤ dDen) (hf : NumeratorRep vk den f a) :
    RationalRep vk f a dDen :=
  let ⟨num, hd, hagree⟩ := hf
  ⟨num, den, hmem, hd, hden, hagree⟩

end NumeratorRep

/-- Weaken both degree bounds of a packaged representation. -/
theorem RationalRep.mono {shape : Shape} {G : Type*} {vk : VerifyingKey shape Fp G}
    {f : Point shape → Fp} {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b')
    (h : RationalRep vk f a b) : RationalRep vk f a' b' :=
  let ⟨num, den, hmem, hnum, hden, hagree⟩ := h
  ⟨num, den, hmem, hnum.trans ha, hden.trans hb, hagree⟩

end Zcash.Snark
