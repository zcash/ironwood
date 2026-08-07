import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Fingerprint.Rational.GroupingTable
import Zcash.Snark.Fingerprint.Rational.OpeningWalk

/-!
# The `other` term list, and the fixed functions behind it

`Msm.coeffAt (.term t)` reads position `t` of the assembled `other` stream, so the ε theorem
needs one fixed function per position rather than a permutation-quotient view. This module
builds towards that list; `Capstone.lean` proves the assembled stream equals it on the good
event.

* The stream lemmas compute `other` through every assembly stage: `ipaFold` prepends the round
  pairs and `ξ`, `multiopenCombine` scales the accumulated stream by `x₄` and appends each
  compressed set, `compressSet` prepends a point member's `x₁`-power and appends the vanishing
  member's `h`-piece block, and `vanishingHCommitment` carries the `xⁿ`-powers.
* `assembleQueries_commitment_char` pins which member is the MSM: on the good event every
  member's commitment constructor is fixed data (`refKind`), and the one `.msm` member is the
  vanishing `h` commitment.
* The mirrors — `mirrorPointFns`, `mirrorMsmFns`, `mirrorBlocks`, `ipaPrefixFns` — rebuild the
  stream as `otherCoeffFns`, one fixed list of represented functions, with `otherLen` its length.

Bases pass through every operation here untouched; only the coefficients are transformed.
-/

namespace Zcash.Snark

open MvPolynomial
open Zcash.Arithmetic (Msm)

/-! ## `other`-projections of the MSM operations -/

section StreamOps

variable {k : ℕ} {F G : Type*}

@[simp] theorem appendTerm_other (c : F) (P : G) (m : Msm k F G) :
    (m.appendTerm c P).other = (c, P) :: m.other := rfl

@[simp] theorem scale_other [Mul F] (c : F) (m : Msm k F G) :
    (Msm.scale c m).other = m.other.map fun t => (c * t.1, t.2) := rfl

@[simp] theorem add_other [Add F] (m₁ m₂ : Msm k F G) :
    (m₁.add m₂).other = m₁.other ++ m₂.other := rfl

@[simp] theorem addToGScalars_other [Add F] [Zero F] (l : List F) (m : Msm k F G) :
    (m.addToGScalars l).other = m.other := rfl

@[simp] theorem addToUScalar_other [Add F] (c : F) (m : Msm k F G) :
    (m.addToUScalar c).other = m.other := rfl

@[simp] theorem addToWScalar_other [Add F] (c : F) (m : Msm k F G) :
    (m.addToWScalar c).other = m.other := rfl

/-- Scaling's coefficient stream is the scaled coefficient stream. -/
theorem scale_other_map_fst [Mul F] (c : F) (m : Msm k F G) :
    ((Msm.scale c m).other.map Prod.fst) = m.other.map fun t => c * t.1 := by
  simp [List.map_map, Function.comp_def]

end StreamOps

/-! ## The `other` list through the assembly stages -/

section StreamLemmas

variable {k : ℕ} {F G : Type*} [Field F]

/-- The per-round fold prepends `(uⱼ, Rⱼ), (uⱼ⁻¹, Lⱼ)` in reverse round order. -/
theorem foldl_appendTerm_pair_other (l : List ((G × G) × F)) :
    ∀ m : Msm k F G,
      (l.foldl (fun acc p => (acc.appendTerm p.2⁻¹ p.1.1).appendTerm p.2 p.1.2) m).other
        = (l.reverse.flatMap fun p => [(p.2, p.1.2), (p.2⁻¹, p.1.1)]) ++ m.other := by
  induction l with
  | nil => intro m; simp
  | cons a t ih =>
    intro m
    rw [List.foldl_cons, ih, List.reverse_cons, List.flatMap_append]
    simp [List.append_assoc]

/-- The IPA fold's term list: the round pairs in reverse order, the blinding term, then the
incoming multiopen terms. -/
theorem ipaFold_other (x v c f xi z : F) (u : List F) (S : G) (rounds : List (G × G))
    (m : Msm k F G) :
    (ipaFold x v c f xi z u S rounds m).other
      = ((rounds.zip u).reverse.flatMap fun p => [(p.2, p.1.2), (p.2⁻¹, p.1.1)])
        ++ (xi, S) :: m.other := by
  simp only [ipaFold, addToGScalars_other, addToUScalar_other, addToWScalar_other,
    foldl_appendTerm_pair_other, appendTerm_other]

/-- The vanishing `h` commitment's coefficient stream: the `xⁿ`-powers, ascending. -/
theorem scaleAppend_fold_other_map_fst (xn : F) (l : List G) :
    ∀ acc : Msm k F G,
      ((l.foldl (fun acc c => (acc.scale xn).appendTerm 1 c) acc).other.map Prod.fst)
        = (List.range l.length).map (fun i => xn ^ i)
          ++ (acc.other.map Prod.fst).map (fun c => xn ^ l.length * c) := by
  induction l with
  | nil =>
    intro acc
    simp
  | cons a t ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp only [appendTerm_other, List.map_cons, scale_other, List.map_map, List.length_cons,
      List.range_succ, List.map_append, List.append_assoc, mul_one]
    congr 1
    congr 1
    refine List.map_congr_left fun t' _ => ?_
    simp only [Function.comp_apply]
    rw [pow_succ]
    ring

/-- `vanishingHCommitment`'s coefficient stream is `[xn⁰, …, xn^(P−1)]`. -/
theorem vanishingHCommitment_other_map_fst (xn : F) (hs : List G) :
    ((vanishingHCommitment k xn hs).other.map Prod.fst)
      = (List.range hs.length).map (fun i => xn ^ i) := by
  rw [vanishingHCommitment]
  rw [scaleAppend_fold_other_map_fst]
  simp [Msm.zero]

/-- The point-member coefficients of one set's compression, in processing order: the running
`x₁`-power at each `.point` member. -/
def pointCoeffs (x1 : F) : List (CommitmentRef k F G × List F) → F → List F
  | [], _ => []
  | (c, _) :: rest, pow =>
    match c with
    | .point _ => pow :: pointCoeffs x1 rest (pow * x1)
    | .msm _ => pointCoeffs x1 rest (pow * x1)

/-- The MSM-member coefficient blocks of one set's compression: each `.msm` member's stream,
scaled by the running `x₁`-power, in processing order. -/
def msmCoeffs (x1 : F) : List (CommitmentRef k F G × List F) → F → List F
  | [], _ => []
  | (c, _) :: rest, pow =>
    match c with
    | .point _ => msmCoeffs x1 rest (pow * x1)
    | .msm mm => (mm.other.map fun t => pow * t.1) ++ msmCoeffs x1 rest (pow * x1)

/-- The compression fold's coefficient stream: reversed point coefficients, then the incoming
stream, then the MSM blocks. -/
theorem compress_fold_other_map_fst (x1 : F) (mems : List (CommitmentRef k F G × List F)) :
    ∀ (m : Msm k F G) (evs : List F) (pow : F),
      ((mems.foldl (fun (st : Msm k F G × List F × F) qc =>
          (accumulateCommitment st.2.2 qc.1 st.1,
           (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
           st.2.2 * x1)) (m, evs, pow)).1.other.map Prod.fst)
        = (pointCoeffs x1 mems pow).reverse ++ (m.other.map Prod.fst)
          ++ msmCoeffs x1 mems pow := by
  induction mems with
  | nil =>
    intro m evs pow
    simp [pointCoeffs, msmCoeffs]
  | cons qc rest ih =>
    intro m evs pow
    obtain ⟨c, evsQ⟩ := qc
    rw [List.foldl_cons]
    cases c with
    | point p =>
      rw [ih]
      simp only [accumulateCommitment, appendTerm_other, List.map_cons, pointCoeffs, msmCoeffs,
        List.reverse_cons, List.append_assoc, List.singleton_append]
    | msm mm =>
      rw [ih]
      simp only [accumulateCommitment, add_other, List.map_append, scale_other_map_fst,
        pointCoeffs, msmCoeffs, List.append_assoc]

/-- One compressed set's coefficient stream. -/
theorem compressSet_fst_other_map_fst (x1 : F) (mems : List (CommitmentRef k F G × List F))
    (numPoints : ℕ) :
    ((compressSet x1 mems numPoints).1.other.map Prod.fst)
      = (pointCoeffs x1 mems 1).reverse ++ msmCoeffs x1 mems 1 := by
  rw [compressSet]
  have h := compress_fold_other_map_fst x1 mems (Msm.zero k F G)
    (List.replicate numPoints (0 : F)) 1
  simpa [Msm.zero] using h

/-- The `x₄`-collapse's appended blocks: each set's terms, scaled by the power of `x₄` matching
its distance from the end. -/
def combineBlocks (x4 : F) : List (Msm k F G) → List (F × G)
  | [] => []
  | qc :: rest => (qc.other.map fun t => (x4 ^ rest.length * t.1, t.2)) ++ combineBlocks x4 rest

/-- The `x₄`-collapse fold's term list: the seed scaled by the full `x₄`-power, then the blocks. -/
theorem combine_fold_fst_other (x4 : F) (l : List (Msm k F G × F)) :
    ∀ (m : Msm k F G) (e : F),
      ((l.foldl (fun (st : Msm k F G × F) p => ((st.1.scale x4).add p.1, st.2 * x4 + p.2))
          (m, e)).1).other
        = (m.other.map fun t => (x4 ^ l.length * t.1, t.2))
          ++ combineBlocks x4 (l.map Prod.fst) := by
  induction l with
  | nil =>
    intro m e
    simp [combineBlocks]
  | cons a t ih =>
    intro m e
    rw [List.foldl_cons, ih]
    simp only [add_other, scale_other, List.map_append, List.map_map, List.map_cons,
      combineBlocks, List.length_cons, List.length_map, List.append_assoc]
    congr 1
    refine List.map_congr_left fun t' _ => ?_
    simp only [Function.comp_apply]
    rw [pow_succ]
    ring_nf

end StreamLemmas

/-! ## Which member is the MSM: the commitment characterization -/

section CommitmentChar

variable {shape : Shape} {G : Type*} [Inhabited G]

/-- Every assembled query either is the vanishing member — slot identity `.vanishingH`,
commitment the folded `h` MSM — or is a plain point commitment with a different identity. -/
theorem assembleQueries_commitment_char (vk : VerifyingKey shape Fp G)
    (ic : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) :
    ∀ q ∈ assembleQueries vk ic ps ch,
      (q.commId = .vanishingH
          ∧ q.commitment = .msm (vanishingHCommitment shape.k (ch.x ^ vk.n)
              (List.ofFn ps.hPieces)))
        ∨ (q.commId ≠ .vanishingH ∧ ∃ g, q.commitment = .point g) := by
  intro q hq
  rw [assembleQueries] at hq
  simp only [List.mem_append] at hq
  rcases hq with ((hq | hq) | hq) | hq
  · -- the per-proof blocks: four point-commitment builders
    obtain ⟨l, hl, hql⟩ := List.mem_flatten.mp hq
    obtain ⟨p, -, rfl⟩ := List.mem_ofFn.mp hl
    simp only [List.mem_append] at hql
    rcases hql with ((hql | hql) | hql) | hql
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hql
      exact Or.inr ⟨by simp, _, rfl⟩
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hql
      exact Or.inr ⟨by simp, _, rfl⟩
    · rw [permutationQueries] at hql
      simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_filterMap] at hql
      rcases hql with ⟨s, -, rfl | rfl⟩ | ⟨s, -, hmap⟩
      · exact Or.inr ⟨by simp, _, rfl⟩
      · exact Or.inr ⟨by simp, _, rfl⟩
      · obtain ⟨le, -, rfl⟩ := Option.map_eq_some_iff.mp hmap
        exact Or.inr ⟨by simp, _, rfl⟩
    · rw [lookupQueries] at hql
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hql
      obtain ⟨l', -, hq5⟩ := hql
      rcases hq5 with rfl | rfl | rfl | rfl | rfl <;> exact Or.inr ⟨by simp, _, rfl⟩
  · -- the fixed columns
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hq
    exact Or.inr ⟨by simp, _, rfl⟩
  · -- the common permutation columns
    rw [permutationCommonQueries] at hq
    obtain ⟨ce, -, rfl⟩ := List.mem_map.mp hq
    exact Or.inr ⟨by simp, _, rfl⟩
  · -- the vanishing block: the `h` MSM, then the random-poly point
    rw [vanishingQueries] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨by simp, _, rfl⟩

end CommitmentChar

/-! ## The fixed mirrors of the `other` stream -/

section Mirrors

variable (shape : Shape) {G : Type*} (vk : VerifyingKey shape Fp G)

/-- Whether a reference member decodes to the vanishing `h` MSM: its flat position carries the
`.vanishingH` slot identity. Out-of-range positions read the `.randomPoly` default, so the kind
is `false` there. -/
def refKind : CommitmentRef shape.k ℕ ℕ → Bool
  | .point n => decide ((queryCommIds shape vk).getD n .randomPoly = .vanishingH)
  | .msm _ => false

/-- The mirror of `pointCoeffs` over the fixed reference members: the running `x₁`-power
functions at the point members. -/
def mirrorPointFns : List (CommitmentRef shape.k ℕ ℕ × List ℕ) → (Point shape → Fp)
    → List (Point shape → Fp)
  | [], _ => []
  | (c, _) :: rest, powf =>
    if refKind shape vk c then
      mirrorPointFns rest (fun pt => powf pt * pt ScalarSlot.x1)
    else
      powf :: mirrorPointFns rest (fun pt => powf pt * pt ScalarSlot.x1)

/-- The mirror of `msmCoeffs`: the vanishing member's `xⁿ`-power block times the running
`x₁`-power. -/
def mirrorMsmFns : List (CommitmentRef shape.k ℕ ℕ × List ℕ) → (Point shape → Fp)
    → List (Point shape → Fp)
  | [], _ => []
  | (c, _) :: rest, powf =>
    if refKind shape vk c then
      (List.range shape.numQuotientPieces).map
          (fun i => fun pt => powf pt * (pt ScalarSlot.x ^ vk.n) ^ i)
        ++ mirrorMsmFns rest (fun pt => powf pt * pt ScalarSlot.x1)
    else
      mirrorMsmFns rest (fun pt => powf pt * pt ScalarSlot.x1)

/-- One reference set's compressed coefficient stream, mirrored. -/
def setFns (si : ℕ) : List (Point shape → Fp) :=
  (mirrorPointFns shape vk ((refSetsL shape vk).getD si []) (fun _ => 1)).reverse
    ++ mirrorMsmFns shape vk ((refSetsL shape vk).getD si []) (fun _ => 1)

/-- The mirror of `combineBlocks`: each set's functions scaled by its `x₄`-power. -/
def mirrorBlocks : List (List (Point shape → Fp)) → List (Point shape → Fp)
  | [] => []
  | fns :: rest =>
    fns.map (fun f => fun pt => pt ScalarSlot.x4 ^ rest.length * f pt) ++ mirrorBlocks rest

/-- The IPA prefix: per round, in reverse order, the challenge and its inverse. -/
def ipaPrefixFns : List (Point shape → Fp) :=
  (List.finRange shape.k).reverse.flatMap
    (fun j => [fun pt => pt (ScalarSlot.ipaRound j), fun pt => (pt (ScalarSlot.ipaRound j))⁻¹])

/-- The collapsed `q'` coefficient: the full `x₄`-power on the seed term. -/
def qPrimeCoeffFn : Point shape → Fp := fun pt => pt ScalarSlot.x4 ^ numSetsD shape vk * 1

/-- **The fixed coefficient-function list of the assembled `other` terms**, positionally: the
IPA prefix, the blinding coefficient `ξ`, the collapsed `q'` coefficient, then the per-set
blocks. On the good event the assembled coefficient stream is exactly this list evaluated at the
sample point (`assembleAt_other_map_fst`). -/
def otherCoeffFns : List (Point shape → Fp) :=
  ipaPrefixFns shape ++ [fun pt => pt ScalarSlot.xi] ++ [qPrimeCoeffFn shape vk]
    ++ mirrorBlocks shape ((List.range (numSetsD shape vk)).map (setFns shape vk))

/-- The assembled `other` length: the mirror's length, a verifying-key constant. -/
def otherLen : ℕ := (otherCoeffFns shape vk).length

end Mirrors

end Zcash.Snark
