import Zcash.Snark.Soundness.BindingReduction

/-!
# Algebraic-group-model wrapper for the binding relation

The deployed soundness capstones end in
`S ∨ HasNontrivialRelation g U W`: a proof either satisfies the intended relation or exhibits a
nontrivial discrete-log relation among the augmented bases `(g, U, W)`. In a prime-order group such
relations exist propositionally; the security content is computational: an efficient adversary should not
be able to *find* one.

This module records the small AGM-facing layer that consumes that relation branch. It follows the useful
part of ArkLib's AGM scaffold: group elements are paired with representations over a public basis. We do
not model an oracle machine for adversaries here. The load-bearing theorem is the deterministic adapter:
if all non-challenge bases have known discrete logs with respect to a base `B`, then any found augmented
relation with a nonzero coefficient on the challenge target recovers the target's discrete log.

The remaining probabilistic wrapper — placing the DL challenge into a random basis slot and accounting for
the chance that the relation's coefficient there is nonzero — is the computational reduction layer outside
this algebraic core.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]


/-- Evaluate an AGM representation over an arbitrary finite public basis. -/
def representationEval {ι : Type*} [Fintype ι] (basis : ι → G) (coeffs : ι → F) : G :=
  ∑ i, coeffs i • basis i

/-- An AGM representation of `target` over `basis`: coefficients whose MSM evaluates to `target`.

In the algebraic-prover model this is the data every prover-output group element carries; wiring the
deployed prover to actually *emit* these (rather than conjuring them by choice) is the remaining
scope of issue #15. -/
structure GroupRepresentation {ι : Type*} [Fintype ι] (basis : ι → G) (target : G) where
  coeffs : ι → F
  hEq : representationEval basis coeffs = target

/-- A group element bundled with an AGM representation over `basis`. Awaits the algebraic-prover
model (issue #15): nothing in the present development produces these from an actual prover run. -/
structure AlgebraicPoint {ι : Type*} [Fintype ι] (basis : ι → G) where
  point : G
  repr : GroupRepresentation (F := F) basis point

namespace AlgebraicPoint

/-- The coefficients carried by an algebraic point. -/
def coeffs {ι : Type*} [Fintype ι] {basis : ι → G}
    (P : AlgebraicPoint (F := F) basis) : ι → F :=
  P.repr.coeffs

@[simp] theorem hEq {ι : Type*} [Fintype ι] {basis : ι → G}
    (P : AlgebraicPoint (F := F) basis) :
    representationEval basis P.coeffs = P.point :=
  P.repr.hEq

end AlgebraicPoint

/-- `representationEval` specializes to the existing `commitGen` MSM over `Fin n`. -/
theorem representationEval_fin {n : ℕ} (basis : Fin n → G) (coeffs : Fin n → F) :
    representationEval basis coeffs = commitGen basis coeffs := rfl

/-- A point represented by one scalar multiple of a base. This is the plain discrete-log artifact.

A DL-hardness reading of this artifact presumes `B ≠ 0` (a generator of the prime-order group): for
`B = 0` the type is inhabited only by `target = 0`, and for `target = 0` it is trivially inhabited by
`log = 0`. -/
structure DiscreteLogRepresentation (B target : G) where
  log : F
  hEq : log • B = target

/-- The scalar contribution of the URS-generator part of an augmented relation after substituting known
discrete logs `gLog i` for each `g i = gLog i • B`. -/
def relationGLog {n : ℕ} (gLog a : Fin n → F) : F :=
  commitGen gLog a

/-- If each `gᵢ` is represented as `gLogᵢ • B`, then the URS part of the augmented relation is represented
by the scalar MSM of those logs. -/
theorem commitGen_of_base_logs {n : ℕ} (B : G) (gLog a : Fin n → F) :
    commitGen (fun i => gLog i • B) a = relationGLog gLog a • B := by
  simp [relationGLog, commitGen, Finset.sum_smul, smul_smul, smul_eq_mul]

/-- The explicit witness form of `HasNontrivialRelation`: coefficients plus the proof that their
augmented MSM vanishes. In the AGM this is what an algebraic adversary's output would provide; in
the present development it is recovered from the existential predicate by choice
(`relationWitnessOfHasNontrivialRelation`), which carries no computational content. -/
structure AugmentedRelationWitness {n : ℕ} (g : Fin n → G) (U W : G) where
  a : Fin n → F
  alpha : F
  beta : F
  nontrivial : a ≠ 0 ∨ alpha ≠ 0 ∨ beta ≠ 0
  relation : commitGen g a + alpha • U + beta • W = 0

/-- The augmented basis index: URS-generator slots plus two slots for `U` and `W`. -/
abbrev AugmentedIndex (n : ℕ) := Sum (Fin n) (Fin 2)

namespace AugmentedIndex

/-- The slot for a URS generator. -/
def gen {n : ℕ} (i : Fin n) : AugmentedIndex n := Sum.inl i

/-- The slot for `U`. -/
def u {n : ℕ} : AugmentedIndex n := Sum.inr 0

/-- The slot for `W`. -/
def w {n : ℕ} : AugmentedIndex n := Sum.inr 1

end AugmentedIndex

/-- Interpret the augmented index as the public basis `(g, U, W)`. -/
def augmentedBasis {n : ℕ} (g : Fin n → G) (U W : G) : AugmentedIndex n → G
  | Sum.inl i => g i
  | Sum.inr j => if j = 0 then U else W

/-- The coefficients of an augmented relation as one representation vector. -/
def augmentedCoeffs {n : ℕ} (a : Fin n → F) (alpha beta : F) : AugmentedIndex n → F
  | Sum.inl i => a i
  | Sum.inr j => if j = 0 then alpha else beta

/-- Evaluating an augmented representation is the augmented MSM used by `HasNontrivialRelation`. -/
theorem representationEval_augmentedBasis {n : ℕ} (g : Fin n → G) (U W : G)
    (a : Fin n → F) (alpha beta : F) :
    representationEval (augmentedBasis g U W) (augmentedCoeffs a alpha beta) =
      commitGen g a + alpha • U + beta • W := by
  simp [representationEval, augmentedBasis, augmentedCoeffs, commitGen, Fintype.sum_sum_type,
    add_assoc]

namespace AugmentedRelationWitness

/-- The same relation witness, viewed as an AGM representation of zero over the augmented basis. -/
def toGroupRepresentation {n : ℕ} {g : Fin n → G} {U W : G}
    (r : AugmentedRelationWitness (F := F) g U W) :
    GroupRepresentation (F := F) (augmentedBasis g U W) (0 : G) :=
  { coeffs := augmentedCoeffs r.a r.alpha r.beta
    hEq := by
      rw [representationEval_augmentedBasis, r.relation] }

end AugmentedRelationWitness

/-- Explicit witnesses and the existential relation predicate are equivalent. -/
theorem augmentedRelationWitness_iff_hasNontrivialRelation {n : ℕ} (g : Fin n → G) (U W : G) :
    Nonempty (AugmentedRelationWitness (F := F) g U W) ↔
      HasNontrivialRelation (F := F) g U W := by
  constructor
  · rintro ⟨r⟩
    exact ⟨r.a, r.alpha, r.beta, r.nontrivial, r.relation⟩
  · rintro ⟨a, alpha, beta, hnt, hrel⟩
    exact ⟨⟨a, alpha, beta, hnt, hrel⟩⟩

/-- Deterministic AGM-to-DL adapter for a relation whose pre-fixed challenge target is `U` — the
`challenge := AugmentedIndex.u` instance of the fixed-slot embedding, with the known logs given
directly on `g` and `W`.

If every URS generator and `W` have known logs over `B`, then an augmented relation
`⟨a,g⟩ + alpha·U + beta·W = 0` with `alpha ≠ 0` recovers the discrete log of `U` over `B`. -/
def discreteLogOfU_of_augmentedRelation {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (gLog : Fin n → F) (wLog : F) (r : AugmentedRelationWitness (F := F) g U W)
    (hg : ∀ i, g i = gLog i • B) (hW : W = wLog • B) (halpha : r.alpha ≠ 0) :
    DiscreteLogRepresentation (F := F) B U := by
  subst W
  let known : F := relationGLog gLog r.a + r.beta * wLog
  refine ⟨r.alpha⁻¹ * (-known), ?_⟩
  have hgpart : commitGen g r.a = relationGLog gLog r.a • B := by
    calc
      commitGen g r.a = commitGen (fun i => gLog i • B) r.a := by
        congr 1
        funext i
        exact hg i
      _ = relationGLog gLog r.a • B := commitGen_of_base_logs B gLog r.a
  have hknown : commitGen g r.a + r.beta • (wLog • B) = known • B := by
    rw [hgpart]
    dsimp only [known]
    rw [add_smul, smul_smul]
  have hzero : known • B + r.alpha • U = 0 := by
    rw [← hknown]
    simpa [add_assoc, add_left_comm, add_comm] using r.relation
  have hmul : r.alpha • U = (-known) • B := by
    have hzero' : r.alpha • U + known • B = 0 := by
      simpa [add_comm] using hzero
    calc
      r.alpha • U = -(known • B) := by
        exact eq_neg_of_add_eq_zero_left hzero'
      _ = (-known) • B := by rw [neg_smul]
  have hscale := congrArg ((fun X : G => (r.alpha)⁻¹ • X)) hmul
  have hlog : U = (r.alpha⁻¹ * (-known)) • B := by
    simpa [smul_smul, inv_mul_cancel₀ halpha] using hscale
  exact hlog.symm

/-- Deterministic AGM-to-DL adapter for a relation whose pre-fixed challenge target is `W` — the
`challenge := AugmentedIndex.w` instance of the fixed-slot embedding, with the known logs given
directly on `g` and `U`. -/
def discreteLogOfW_of_augmentedRelation {n : ℕ} (B : G) (g : Fin n → G) (U W : G)
    (gLog : Fin n → F) (uLog : F) (r : AugmentedRelationWitness (F := F) g U W)
    (hg : ∀ i, g i = gLog i • B) (hU : U = uLog • B) (hbeta : r.beta ≠ 0) :
    DiscreteLogRepresentation (F := F) B W := by
  subst U
  let known : F := relationGLog gLog r.a + r.alpha * uLog
  refine ⟨r.beta⁻¹ * (-known), ?_⟩
  have hgpart : commitGen g r.a = relationGLog gLog r.a • B := by
    calc
      commitGen g r.a = commitGen (fun i => gLog i • B) r.a := by
        congr 1
        funext i
        exact hg i
      _ = relationGLog gLog r.a • B := commitGen_of_base_logs B gLog r.a
  have hknown : commitGen g r.a + r.alpha • (uLog • B) = known • B := by
    rw [hgpart]
    dsimp only [known]
    rw [add_smul, smul_smul]
  have hzero : known • B + r.beta • W = 0 := by
    rw [← hknown]
    simpa [add_assoc, add_left_comm, add_comm] using r.relation
  have hmul : r.beta • W = (-known) • B := by
    have hzero' : r.beta • W + known • B = 0 := by
      simpa [add_comm] using hzero
    calc
      r.beta • W = -(known • B) := by
        exact eq_neg_of_add_eq_zero_left hzero'
      _ = (-known) • B := by rw [neg_smul]
  have hscale := congrArg ((fun X : G => (r.beta)⁻¹ • X)) hmul
  have hlog : W = (r.beta⁻¹ * (-known)) • B := by
    simpa [smul_smul, inv_mul_cancel₀ hbeta] using hscale
  exact hlog.symm

end Zcash.Snark
