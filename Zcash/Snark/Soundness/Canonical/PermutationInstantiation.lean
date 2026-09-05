import Zcash.Common.RelationWitness
import Zcash.Snark.Soundness.Multiopen.ConstraintResolver
import Zcash.Snark.Soundness.Argument.PermutationRows

/-!
# Instantiating permutation constraints with routed decoded polynomials

The permutation verifier describes each chunk through evaluation references:

* a `ColumnRef` indexes the instance, advice, or fixed query layout;
* the accompanying natural number indexes a common permutation (`σ`) column;
* the chunk position indexes the permutation running-product commitment.

This file resolves those three index spaces to `CommitmentId`s and hence to one polynomial
resolver.  The construction is generic in the verification key, proof string, and resolver; the
decoded multiopen resolver is one downstream instance.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

open CompPoly.CPolynomial

set_option maxHeartbeats 20000

@[ext]
theorem PermSetEval.ext {F : Type*} {a b : PermSetEval F}
    (heval : a.eval = b.eval) (hnext : a.nextEval = b.nextEval)
    (hlast : a.lastEval = b.lastEval) : a = b := by
  cases a
  cases b
  simp_all

/-- The commitment identity selected by a permutation column's evaluation reference.  The
reference indexes an evaluation/query-layout entry, whose first component is the committed column
index. -/
def permutationColumnCommitmentId
    {shape : CircuitShape} {numProofs : ℕ} {F G : Type*}
    (vk : VerifyingKey shape F G) (p : Fin numProofs) : ColumnRef → CommitmentId
  | .advice i => .adviceCol p (vk.adviceQueryLayout.getD i (0, 0)).1
  | .fixed i => .fixedCol (vk.fixedQueryLayout.getD i (0, 0)).1
  | .instance i => .instanceCol p (vk.instanceQueryLayout.getD i (0, 0)).1

/-- A permutation value-column reference is usable at the unrotated challenge `x`: its evaluation
index and query-layout entry are in range, and that layout entry has rotation zero. -/
def PermutationColumnRef.Coherent {shape : CircuitShape} {F G : Type*}
    (vk : VerifyingKey shape F G) : ColumnRef → Prop
  | .advice i =>
      i < shape.numAdviceQueries ∧ i < vk.adviceQueryLayout.length ∧
        (vk.adviceQueryLayout.getD i (0, 0)).2 = 0
  | .fixed i =>
      i < shape.numFixedQueries ∧ i < vk.fixedQueryLayout.length ∧
        (vk.fixedQueryLayout.getD i (0, 0)).2 = 0
  | .instance i =>
      i < shape.numInstanceQueries ∧ i < vk.instanceQueryLayout.length ∧
        (vk.instanceQueryLayout.getD i (0, 0)).2 = 0

/-- VK coherence needed to route every `(value, σ-name)` pair in every permutation chunk. -/
def PermutationChunkRoutingCoherent {shape : CircuitShape} {F G : Type*}
    (vk : VerifyingKey shape F G) : Prop :=
  ∀ chunk ∈ vk.permutationChunks, ∀ ref ∈ chunk,
    PermutationColumnRef.Coherent vk ref.1 ∧ ref.2 < shape.numPermutationColumns

/-- Resolve a permutation column reference to its polynomial.  `finFn` mirrors the verifier's
total claimed-evaluation feeds: an out-of-range evaluation reference reads zero. -/
def permutationColumnPolynomialOfResolver
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (cr : ColumnRef) : CPoly :=
  cr.resolve
    (finFn fun i : Fin shape.numInstanceQueries =>
      poly (permutationColumnCommitmentId vk p (.instance i)))
    (finFn fun i : Fin shape.numAdviceQueries =>
      poly (permutationColumnCommitmentId vk p (.advice i)))
    (finFn fun i : Fin shape.numFixedQueries =>
      poly (permutationColumnCommitmentId vk p (.fixed i)))

/-- The polynomial-valued evaluation record for one permutation running product.  Its optional
last-row opening follows the shape-level Halo2 read schedule. -/
def permutationSetOfResolver
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (s : Fin shape.numPermutationSets) :
    PermSetEval (CPoly) :=
  { eval := poly (.permProduct p s)
    nextEval := comp (poly (.permProduct p s)) (C vk.omega * X)
    lastEval :=
      if s.val + 1 = shape.numPermutationSets then none
      else some (comp (poly (.permProduct p s))
        (C (vk.omega ^ (-((vk.blindingFactors : ℤ) + 1))) * X)) }

/-- One sub-proof's permutation running products, in verifier order. -/
def permutationSetsOfResolver
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) : List (PermSetEval (CPoly)) :=
  List.ofFn fun s => permutationSetOfResolver vk poly p s

/-- One sub-proof's permutation chunks, with the value and common-permutation columns selected by
their stable commitment identities. -/
def permutationChunksOfResolver
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) :
    List (PermSetEval (CPoly) × List (CPoly × CPoly)) :=
  ((permutationSetsOfResolver vk poly p).zip vk.permutationChunks).map fun sc =>
    (sc.1, sc.2.map fun cr =>
      (permutationColumnPolynomialOfResolver vk poly p cr.1, poly (.permCommon cr.2)))

/-- The value/σ polynomial pairs of chunk `c`, totalized by the empty chunk out of range. -/
def permutationChunkPairsOfResolver
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (c : ℕ) : List (CPoly × CPoly) :=
  (vk.permutationChunks.getD c []).map fun cr =>
    (permutationColumnPolynomialOfResolver vk poly p cr.1, poly (.permCommon cr.2))

@[simp] theorem permutationSetsOfResolver_length
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) :
    (permutationSetsOfResolver vk poly p).length = shape.numPermutationSets := by
  simp [permutationSetsOfResolver]

theorem permutationChunksOfResolver_length
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) :
    (permutationChunksOfResolver vk poly p).length =
      min shape.numPermutationSets vk.permutationChunks.length := by
  simp [permutationChunksOfResolver]

/-- In-range chunk lookup exposes the corresponding running-product set and routed pair list. -/
theorem permutationChunksOfResolver_getElem
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) {c : ℕ}
    (hcs : c < shape.numPermutationSets) (hcv : c < vk.permutationChunks.length) :
    (permutationChunksOfResolver vk poly p)[c]'(by
      rw [permutationChunksOfResolver_length]
      omega) =
      (permutationSetOfResolver vk poly p ⟨c, hcs⟩,
        permutationChunkPairsOfResolver vk poly p c) := by
  simp [permutationChunksOfResolver, permutationSetsOfResolver,
    permutationChunkPairsOfResolver, hcv]

/-- The verifier's permutation-product query block for one sub-proof. -/
def subProofPermutationQueries {shape : Shape} {F G : Type*} [Field F]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (p : Fin shape.numProofs) :
    List (VerifierQuery shape.k F G) :=
  permutationQueries ch.x (rotateOmega vk.omega ch.x 1)
    (rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1)))
    (CommitmentId.permProduct p)
    (List.ofFn fun s => (ps.permutationProduct p s, ps.permutationSetEvals p s))

/-- Every per-proof permutation-product query occurs in the complete assembled query list. -/
theorem mem_assembleQueries_of_mem_subProofPermutationQueries
    {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (p : Fin shape.numProofs) {q : VerifierQuery shape.k F G}
    (hq : q ∈ subProofPermutationQueries vk ps ch p) :
    q ∈ assembleQueries vk instanceCommitment ps ch := by
  have hblock : q ∈ subProofOpeningQueries vk instanceCommitment ps ch.x
      (rotateOmega vk.omega ch.x (-1)) (rotateOmega vk.omega ch.x 1)
      (rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1))) p := by
    exact List.mem_append_left _ (List.mem_append_right _ (by
      simpa [subProofPermutationQueries] using hq))
  have hperProof : q ∈ subProofBlocks fun p : Fin shape.numProofs =>
      subProofOpeningQueries vk instanceCommitment ps ch.x
        (rotateOmega vk.omega ch.x (-1)) (rotateOmega vk.omega ch.x 1)
        (rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1))) p := by
    exact List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, hblock⟩
  rw [assembleQueries_parametric_numProofs]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hperProof))

private theorem permutation_eval_query_mem
    {shape : Shape} {F G : Type*} [Field F]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (p : Fin shape.numProofs)
    (s : Fin shape.numPermutationSets) :
    { point := ch.x,
      commitment := .point (ps.permutationProduct p s),
      eval := (ps.permutationSetEvals p s).eval,
      commId := .permProduct p s } ∈ subProofPermutationQueries vk ps ch p := by
  have hindexed :
      ((ps.permutationProduct p s, ps.permutationSetEvals p s), s.val) ∈
        (List.ofFn (fun s =>
          (ps.permutationProduct p s, ps.permutationSetEvals p s))).zip
          (List.range shape.numPermutationSets) := by
    rw [List.mem_iff_getElem]
    refine ⟨s.val, by simp, ?_⟩
    simp
  rw [subProofPermutationQueries, permutationQueries, List.mem_append]
  refine Or.inl (List.mem_flatMap.mpr
    ⟨((ps.permutationProduct p s, ps.permutationSetEvals p s), s.val), ?_, ?_⟩)
  · simpa using hindexed
  · simp

private theorem permutation_next_query_mem
    {shape : Shape} {F G : Type*} [Field F]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (p : Fin shape.numProofs)
    (s : Fin shape.numPermutationSets) :
    { point := rotateOmega vk.omega ch.x 1,
      commitment := .point (ps.permutationProduct p s),
      eval := (ps.permutationSetEvals p s).nextEval,
      commId := .permProduct p s } ∈ subProofPermutationQueries vk ps ch p := by
  have hindexed :
      ((ps.permutationProduct p s, ps.permutationSetEvals p s), s.val) ∈
        (List.ofFn (fun s =>
          (ps.permutationProduct p s, ps.permutationSetEvals p s))).zip
          (List.range shape.numPermutationSets) := by
    rw [List.mem_iff_getElem]
    refine ⟨s.val, by simp, ?_⟩
    simp
  rw [subProofPermutationQueries, permutationQueries, List.mem_append]
  refine Or.inl (List.mem_flatMap.mpr
    ⟨((ps.permutationProduct p s, ps.permutationSetEvals p s), s.val), ?_, ?_⟩)
  · simpa using hindexed
  · simp

private theorem permutation_last_query_mem
    {shape : Shape} {F G : Type*} [Field F]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (p : Fin shape.numProofs)
    (s : Fin shape.numPermutationSets) {lastEval : F}
    (hs : s.val + 1 < shape.numPermutationSets)
    (hlast : (ps.permutationSetEvals p s).lastEval = some lastEval) :
    { point := rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1)),
      commitment := .point (ps.permutationProduct p s),
      eval := lastEval,
      commId := .permProduct p s } ∈ subProofPermutationQueries vk ps ch p := by
  let indexed :=
    (List.ofFn (fun s =>
      (ps.permutationProduct p s, ps.permutationSetEvals p s))).zip
      (List.range shape.numPermutationSets)
  have hindexed :
      ((ps.permutationProduct p s, ps.permutationSetEvals p s), s.val) ∈ indexed := by
    rw [List.mem_iff_getElem]
    refine ⟨s.val, by simp [indexed], ?_⟩
    simp [indexed]
  have hdrop :
      ((ps.permutationProduct p s, ps.permutationSetEvals p s), s.val) ∈
        indexed.dropLast := by
    rw [List.mem_iff_getElem]
    refine ⟨s.val, ?_, ?_⟩
    · simp [indexed]
      omega
    · rw [List.getElem_dropLast]
      simp [indexed]
  rw [subProofPermutationQueries, permutationQueries, List.mem_append]
  refine Or.inr (List.mem_filterMap.mpr
    ⟨((ps.permutationProduct p s, ps.permutationSetEvals p s), s.val), ?_, ?_⟩)
  · simpa [indexed] using hdrop
  · simp [hlast]

/-- The rejecting proof-string check says exactly which permutation products carry a last-row
opening: every non-final set and no final set. -/
theorem permutationLastEval_isSome
    {shape : Shape} {F G : Type*}
    (ps : ProofString shape F G)
    (hwf : permutationLastEvalsWellFormed ps = true)
    (p : Fin shape.numProofs) (s : Fin shape.numPermutationSets) :
    (ps.permutationSetEvals p s).lastEval.isSome =
      decide (s.val + 1 < shape.numPermutationSets) := by
  have hp := List.all_eq_true.mp hwf
    ((List.ofFn fun s : Fin shape.numPermutationSets =>
      if s.val + 1 = shape.numPermutationSets then
        match (ps.permutationSetEvals p s).lastEval with
        | none => true
        | some _ => false
      else
        match (ps.permutationSetEvals p s).lastEval with
        | some _ => true
        | none => false).all id)
    (List.mem_ofFn.mpr ⟨p, rfl⟩)
  have hs := List.all_eq_true.mp hp
    (if s.val + 1 = shape.numPermutationSets then
      match (ps.permutationSetEvals p s).lastEval with
      | none => true
      | some _ => false
    else
      match (ps.permutationSetEvals p s).lastEval with
      | some _ => true
      | none => false)
    (List.mem_ofFn.mpr ⟨s, rfl⟩)
  simp only [id_eq] at hs
  by_cases hfinal : s.val + 1 = shape.numPermutationSets
  · rw [if_pos hfinal] at hs
    have hnot : ¬s.val + 1 < shape.numPermutationSets := by omega
    simp only [hnot]
    cases h : (ps.permutationSetEvals p s).lastEval with
    | none => rfl
    | some v => simp [h] at hs
  · rw [if_neg hfinal] at hs
    have hlt : s.val + 1 < shape.numPermutationSets := by omega
    simp only [hlt]
    cases h : (ps.permutationSetEvals p s).lastEval with
    | none => simp [h] at hs
    | some v => rfl

/-- Evaluating the resolver-backed running-product records at `x` reproduces the proof's claimed
permutation-set evaluations.  All three fields are supplied by the verifier's actual opening
queries; the rejecting well-formedness check supplies the optional last-row schedule. -/
theorem eval_permutationSetsOfResolver
    {shape : Shape} {G : Type*} [Inhabited G]
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hwf : permutationLastEvalsWellFormed ps = true)
    (p : Fin shape.numProofs)
    (hopen : ∀ q ∈ assembleQueries vk instanceCommitment ps ch,
      (poly q.commId).eval q.point = q.eval) :
    (permutationSetsOfResolver vk poly p).map
        (PermSetEval.map fun q => q.eval ch.x)
      = subProofPermSets ps p := by
  rw [permutationSetsOfResolver, subProofPermSets, List.map_ofFn]
  congr 1
  funext s
  have heval := hopen
    { point := ch.x,
      commitment := .point (ps.permutationProduct p s),
      eval := (ps.permutationSetEvals p s).eval,
      commId := .permProduct p s }
    (mem_assembleQueries_of_mem_subProofPermutationQueries
      vk instanceCommitment ps ch p (permutation_eval_query_mem vk ps ch p s))
  have hnext := hopen
    { point := rotateOmega vk.omega ch.x 1,
      commitment := .point (ps.permutationProduct p s),
      eval := (ps.permutationSetEvals p s).nextEval,
      commId := .permProduct p s }
    (mem_assembleQueries_of_mem_subProofPermutationQueries
      vk instanceCommitment ps ch p (permutation_next_query_mem vk ps ch p s))
  apply PermSetEval.ext
  · change (poly (.permProduct p s)).eval ch.x = (ps.permutationSetEvals p s).eval
    simpa using heval
  · change (comp (poly (.permProduct p s)) (C vk.omega * X)).eval ch.x =
      (ps.permutationSetEvals p s).nextEval
    rw [eval_comp_rotate, _root_.mul_comm]
    simpa only [rotateOmega, zpow_one] using hnext
  · have hschedule := permutationLastEval_isSome ps hwf p s
    change
      (if s.val + 1 = shape.numPermutationSets then none
        else some (comp (poly (.permProduct p s))
          (C (vk.omega ^ (-((vk.blindingFactors : ℤ) + 1))) * X))).map
            (fun q : CPoly => q.eval ch.x)
        = (ps.permutationSetEvals p s).lastEval
    by_cases hfinal : s.val + 1 = shape.numPermutationSets
    · have hnot : ¬s.val + 1 < shape.numPermutationSets := by omega
      have hnone : (ps.permutationSetEvals p s).lastEval = none := by
        cases h : (ps.permutationSetEvals p s).lastEval with
        | none => rfl
        | some v => simp [h, hnot] at hschedule
      rw [if_pos hfinal, hnone]
      rfl
    · have hlt : s.val + 1 < shape.numPermutationSets := by omega
      obtain ⟨lastEval, hlast⟩ : ∃ lastEval,
          (ps.permutationSetEvals p s).lastEval = some lastEval := by
        cases h : (ps.permutationSetEvals p s).lastEval with
        | none => simp [h, hlt] at hschedule
        | some v => exact ⟨v, rfl⟩
      have hopenLast := hopen
        { point := rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1)),
          commitment := .point (ps.permutationProduct p s),
          eval := lastEval,
          commId := .permProduct p s }
        (mem_assembleQueries_of_mem_subProofPermutationQueries
          vk instanceCommitment ps ch p
          (permutation_last_query_mem vk ps ch p s hlt hlast))
      rw [if_neg hfinal, hlast]
      simp only [Option.map_some, Option.some.injEq]
      rw [eval_comp_rotate, _root_.mul_comm]
      simpa only [rotateOmega] using hopenLast

/-- A coherent permutation value reference is opened at `x`, and therefore the selected resolver
polynomial evaluates to the proof's claimed column value. -/
theorem eval_permutationColumnPolynomialOfResolver
    {shape : Shape} {G : Type*} [Inhabited G]
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly) (p : Fin shape.numProofs)
    (cr : ColumnRef) (hcr : PermutationColumnRef.Coherent vk cr)
    (hopen : ∀ q ∈ assembleQueries vk instanceCommitment ps ch,
      (poly q.commId).eval q.point = q.eval) :
    (permutationColumnPolynomialOfResolver vk poly p cr).eval ch.x =
      cr.resolve (finFn (ps.instanceEvals p)) (finFn (ps.adviceEvals p))
        (finFn ps.fixedEvals) := by
  cases cr with
  | advice i =>
      rcases hcr with ⟨hi, hil, hrot⟩
      let q : VerifierQuery shape.k Fp G :=
        { point := rotateOmega vk.omega ch.x
            (vk.adviceQueryLayout.getD i (0, 0)).2
          commitment := .point
            ((finFnG (ps.adviceCommitments p))
              (vk.adviceQueryLayout.getD i (0, 0)).1)
          eval := (List.ofFn (ps.adviceEvals p)).getD i 0
          commId := .adviceCol p (vk.adviceQueryLayout.getD i (0, 0)).1 }
      have hq : q ∈ assembleQueries vk instanceCommitment ps ch := by
        have hlocal := columnQuery_getD_mem (k := shape.k) vk.omega ch.x
          (finFnG (ps.adviceCommitments p)) (CommitmentId.adviceCol p)
          vk.adviceQueryLayout (List.ofFn (ps.adviceEvals p)) hil (by simp [hi])
        simp only [assembleQueries]
        refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inl ?_)))))
        refine List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, ?_⟩
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inr (by simpa [q] using hlocal))))))
      have ho := hopen q hq
      dsimp only [q] at ho
      rw [hrot] at ho
      simp only [rotateOmega, zpow_zero, _root_.mul_one] at ho
      simpa [permutationColumnPolynomialOfResolver, permutationColumnCommitmentId,
        ColumnRef.resolve, finFn, hi] using ho
  | fixed i =>
      rcases hcr with ⟨hi, hil, hrot⟩
      let q : VerifierQuery shape.k Fp G :=
        { point := rotateOmega vk.omega ch.x
            (vk.fixedQueryLayout.getD i (0, 0)).2
          commitment := .point (vk.fixedCommitment
            (vk.fixedQueryLayout.getD i (0, 0)).1)
          eval := (List.ofFn ps.fixedEvals).getD i 0
          commId := .fixedCol (vk.fixedQueryLayout.getD i (0, 0)).1 }
      have hq : q ∈ assembleQueries vk instanceCommitment ps ch := by
        have hlocal := columnQuery_getD_mem (k := shape.k) vk.omega ch.x
          vk.fixedCommitment CommitmentId.fixedCol vk.fixedQueryLayout
          (List.ofFn ps.fixedEvals) hil (by simp [hi])
        simp only [assembleQueries]
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (by simpa [q] using hlocal)))
      have ho := hopen q hq
      dsimp only [q] at ho
      rw [hrot] at ho
      simp only [rotateOmega, zpow_zero, _root_.mul_one] at ho
      simpa [permutationColumnPolynomialOfResolver, permutationColumnCommitmentId,
        ColumnRef.resolve, finFn, hi] using ho
  | «instance» i =>
      rcases hcr with ⟨hi, hil, hrot⟩
      let q : VerifierQuery shape.k Fp G :=
        { point := rotateOmega vk.omega ch.x
            (vk.instanceQueryLayout.getD i (0, 0)).2
          commitment := .point
            (instanceCommitment p (vk.instanceQueryLayout.getD i (0, 0)).1)
          eval := (List.ofFn (ps.instanceEvals p)).getD i 0
          commId := .instanceCol p (vk.instanceQueryLayout.getD i (0, 0)).1 }
      have hq : q ∈ assembleQueries vk instanceCommitment ps ch := by
        have hlocal := columnQuery_getD_mem (k := shape.k) vk.omega ch.x
          (instanceCommitment p) (CommitmentId.instanceCol p)
          vk.instanceQueryLayout (List.ofFn (ps.instanceEvals p)) hil (by simp [hi])
        simp only [assembleQueries]
        refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inl ?_)))))
        refine List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, ?_⟩
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inl (by simpa [q] using hlocal))))))
      have ho := hopen q hq
      dsimp only [q] at ho
      rw [hrot] at ho
      simp only [rotateOmega, zpow_zero, _root_.mul_one] at ho
      simpa [permutationColumnPolynomialOfResolver, permutationColumnCommitmentId,
        ColumnRef.resolve, finFn, hi] using ho

/-- A common permutation-column reference is opened at `x`. -/
theorem eval_permutationCommonPolynomialOfResolver
    {shape : Shape} {G : Type*} [Inhabited G]
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly) {i : ℕ}
    (hi : i < shape.numPermutationColumns)
    (hopen : ∀ q ∈ assembleQueries vk instanceCommitment ps ch,
      (poly q.commId).eval q.point = q.eval) :
    (poly (.permCommon i)).eval ch.x = finFn ps.permutationCommonEvals i := by
  let fi : Fin shape.numPermutationColumns := ⟨i, hi⟩
  let q : VerifierQuery shape.k Fp G :=
    { point := ch.x
      commitment := .point (vk.permutationCommonCommitment fi)
      eval := ps.permutationCommonEvals fi
      commId := .permCommon i }
  have hindexed :
      ((vk.permutationCommonCommitment fi, ps.permutationCommonEvals fi), i) ∈
        (List.ofFn (fun c =>
          (vk.permutationCommonCommitment c, ps.permutationCommonEvals c))).zip
          (List.range shape.numPermutationColumns) := by
    rw [List.mem_iff_getElem]
    refine ⟨i, by simp [hi], ?_⟩
    simp [fi]
  have hlocal : q ∈ permutationCommonQueries ch.x CommitmentId.permCommon
      (List.ofFn fun c =>
        (vk.permutationCommonCommitment c, ps.permutationCommonEvals c)) := by
    unfold permutationCommonQueries
    refine List.mem_map.mpr
      ⟨((vk.permutationCommonCommitment fi, ps.permutationCommonEvals fi), i), ?_, ?_⟩
    · simpa using hindexed
    · simp [q, fi]
  have hq : q ∈ assembleQueries vk instanceCommitment ps ch := by
    simp only [assembleQueries]
    exact List.mem_append_left _ (List.mem_append_right _ hlocal)
  simpa [q, fi, finFn, hi] using hopen q hq

/-- Evaluating every resolver-backed `(value, σ-name)` pair in one coherent VK chunk reproduces
the verifier's claimed pair list. -/
theorem eval_permutationChunkPairsOfResolver
    {shape : Shape} {G : Type*} [Inhabited G]
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly) (p : Fin shape.numProofs)
    (chunk : List (ColumnRef × ℕ)) (hchunk : chunk ∈ vk.permutationChunks)
    (hcoherent : PermutationChunkRoutingCoherent vk)
    (hopen : ∀ q ∈ assembleQueries vk instanceCommitment ps ch,
      (poly q.commId).eval q.point = q.eval) :
    (chunk.map fun cr =>
      (permutationColumnPolynomialOfResolver vk poly p cr.1,
        poly (.permCommon cr.2))).map
        (fun pair => (pair.1.eval ch.x, pair.2.eval ch.x))
      = chunk.map fun cr =>
        (cr.1.resolve (finFn (ps.instanceEvals p)) (finFn (ps.adviceEvals p))
          (finFn ps.fixedEvals),
        finFn ps.permutationCommonEvals cr.2) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro cr hcr
  obtain ⟨hvalue, hcommon⟩ := hcoherent chunk hchunk cr hcr
  apply Prod.ext
  · exact eval_permutationColumnPolynomialOfResolver
      vk instanceCommitment ps ch poly p cr.1 hvalue hopen
  · exact eval_permutationCommonPolynomialOfResolver
      vk instanceCommitment ps ch poly hcommon hopen

/-- Evaluating all resolver-backed permutation chunks at `x` reproduces
`subProofPermChunks`, including the running-product records and every value/σ pair. -/
theorem eval_permutationChunksOfResolver
    {shape : Shape} {G : Type*} [Inhabited G]
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hwf : permutationLastEvalsWellFormed ps = true)
    (hcoherent : PermutationChunkRoutingCoherent vk)
    (p : Fin shape.numProofs)
    (hopen : ∀ q ∈ assembleQueries vk instanceCommitment ps ch,
      (poly q.commId).eval q.point = q.eval) :
    (permutationChunksOfResolver vk poly p).map (fun chunk =>
        (chunk.1.map fun q => q.eval ch.x,
          chunk.2.map fun pair => (pair.1.eval ch.x, pair.2.eval ch.x)))
      = subProofPermChunks vk ps p := by
  have hsets := eval_permutationSetsOfResolver
    vk instanceCommitment ps ch poly hwf p hopen
  rw [permutationChunksOfResolver, subProofPermChunks, List.map_map]
  rw [← hsets, List.zip_map_left, List.map_map]
  apply List.map_congr_left
  intro sc hsc
  apply Prod.ext
  · rfl
  · have hchunk : sc.2 ∈ vk.permutationChunks := by
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hsc
      have hir : i < vk.permutationChunks.length := by
        rw [List.length_zip] at hi
        omega
      have hmem :
          (((permutationSetsOfResolver vk poly p).zip vk.permutationChunks)[i]).2 ∈
            vk.permutationChunks := by
        rw [List.getElem_zip]
        exact List.getElem_mem hir
      rw [hget] at hmem
      exact hmem
    exact eval_permutationChunkPairsOfResolver
      vk instanceCommitment ps ch poly p sc.2 hchunk hcoherent hopen

/-- The four divisibility families consumed by
`deployed_perm_copy_constraints_all_chunks`, specialized to one resolver-backed proof. -/
structure ResolverPermutationConstraints
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (l0 lLast lBlind : CPoly)
    (p : Fin numProofs) (n m : ℕ) : Prop where
  step : ∀ c < shape.numPermutationSets, (X ^ n - 1 : CPoly) ∣
    permChunkExpression (C ch.beta) (C ch.gamma) X (C vk.delta) vk.chunkLen c
      (permSetPolys vk.omega (poly (.permProduct p c)) none)
      (permutationChunkPairsOfResolver vk poly p c) lLast lBlind
  chain : ∀ c, c + 1 < shape.numPermutationSets → (X ^ n - 1 : CPoly) ∣
    (poly (.permProduct p (c + 1)) -
      (poly (.permProduct p c)).comp (C (vk.omega ^ m) * X)) * l0
  start : (X ^ n - 1 : CPoly) ∣ l0 * (1 - poly (.permProduct p 0))
  finish : (X ^ n - 1 : CPoly) ∣
    ((poly (.permProduct p (shape.numPermutationSets - 1))) ^ 2 -
      poly (.permProduct p (shape.numPermutationSets - 1))) * lLast

/-- Full polynomial constraint satisfaction supplies the resolver-backed permutation step,
inter-set chain, start, and end constraints.  The two structural premises are VK facts: chunks and
permutation sets have the same count, and the last-row rotation is `ω^m`. -/
theorem ConstraintSatisfaction.resolverPermutationConstraints
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (l0 lLast lBlind : CPoly)
    (p : Fin numProofs) {n m : ℕ}
    (h : ConstraintSatisfaction
      (constraintModelOfResolver (numProofs := numProofs) vk ch poly
        (permutationSetsOfResolver (numProofs := numProofs) vk poly)
        (permutationChunksOfResolver (numProofs := numProofs) vk poly)
        l0 lLast lBlind) n)
    (hnonempty : 0 < shape.numPermutationSets)
    (hchunks : vk.permutationChunks.length = shape.numPermutationSets)
    (hrotation : vk.omega ^ m =
      vk.omega ^ (-((vk.blindingFactors : ℤ) + 1))) :
    ResolverPermutationConstraints vk ch poly l0 lLast lBlind p n m := by
  let sets := permutationSetsOfResolver vk poly p
  let chunks := permutationChunksOfResolver vk poly p
  have hchunksLen : chunks.length = shape.numPermutationSets := by
    rw [permutationChunksOfResolver_length, hchunks, min_self]
  refine
    { step := ?_
      chain := ?_
      start := ?_
      finish := ?_ }
  · intro c hc
    have hcv : c < vk.permutationChunks.length := by omega
    let chunk :=
      (permutationSetOfResolver vk poly p ⟨c, hc⟩,
        permutationChunkPairsOfResolver vk poly p c)
    have hchunk : (c, chunk) ∈ (List.range chunks.length).zip chunks := by
      rw [List.mem_iff_getElem]
      refine ⟨c, by simp [hchunksLen, hc], ?_⟩
      simp only [List.getElem_zip, List.getElem_range]
      rw [show chunks[c]'(by omega) = chunk from by
        simpa only [chunks, chunk] using
          permutationChunksOfResolver_getElem vk poly p hc hcv]
    have hdvd := h.permutationExpression p (permutation_step_mem
      sets chunks (C ch.beta) (C ch.gamma) X (C vk.delta) vk.chunkLen
      l0 lLast lBlind hchunk)
    simpa [constraintModelOfResolver,
      ConstraintPolyModel.permutationConstraints, sets, chunks, chunk,
      permutationSetOfResolver, permSetPolys, permChunkExpression] using hdvd
  · intro c hc
    let current := permutationSetOfResolver vk poly p ⟨c + 1, hc⟩
    let previous := permutationSetOfResolver vk poly p ⟨c, by omega⟩
    have hpair : (current, previous) ∈ (sets.drop 1).zip sets := by
      rw [List.mem_iff_getElem]
      refine ⟨c, ?_, ?_⟩
      · simp [sets]
        omega
      simp [sets, current, previous, permutationSetsOfResolver]
    have hdvd := h.permutationExpression p (permutation_chain_mem
      sets chunks (C ch.beta) (C ch.gamma) X (C vk.delta) vk.chunkLen
      l0 lLast lBlind hpair)
    simpa [constraintModelOfResolver,
      ConstraintPolyModel.permutationConstraints, sets, chunks, current, previous,
      permutationSetOfResolver, hrotation,
      show c + 1 ≠ shape.numPermutationSets by omega] using hdvd
  · let first := permutationSetOfResolver vk poly p ⟨0, hnonempty⟩
    have hfirst : sets.head? = some first := by
      dsimp only [sets]
      rw [permutationSetsOfResolver, List.head?_eq_getElem?, List.getElem?_ofFn]
      simp [hnonempty, first]
    have hdvd := h.permutationExpression p (permutation_start_mem
      sets chunks (C ch.beta) (C ch.gamma) X (C vk.delta) vk.chunkLen
      l0 lLast lBlind hfirst)
    simpa [constraintModelOfResolver,
      ConstraintPolyModel.permutationConstraints, sets, chunks, first,
      permutationSetOfResolver] using hdvd
  · let last := permutationSetOfResolver vk poly p
      ⟨shape.numPermutationSets - 1, by omega⟩
    have hlast : sets.getLast? = some last := by
      dsimp only [sets]
      rw [permutationSetsOfResolver, List.getLast?_eq_getElem?, List.getElem?_ofFn]
      simp [hnonempty, last]
    have hdvd := h.permutationExpression p (permutation_end_mem
      sets chunks (C ch.beta) (C ch.gamma) X (C vk.delta) vk.chunkLen
      l0 lLast lBlind hlast)
    simpa [constraintModelOfResolver,
      ConstraintPolyModel.permutationConstraints, sets, chunks, last,
      permutationSetOfResolver] using hdvd

/-- Successful rejecting assembly supplies the permutation last-evaluation read schedule used by
the resolver-backed set records. -/
theorem permutationLastEvalsWellFormed_of_assemble?_eq_some
    {shape : Shape} {F G : Type*} [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    {m : Msm shape.k F G} (hm : assemble? vk instanceCommitment ps ch = some m) :
    permutationLastEvalsWellFormed ps = true := by
  unfold assemble? at hm
  by_cases hwf : proofStringWellFormed ps = true
  · simpa [proofStringWellFormed] using hwf
  · rw [if_neg hwf] at hm
    exact absurd hm (by simp)

/-- The decoded multiopen resolver simultaneously instantiates the permutation running products
and chunk pairs.  If member-node binding fails, the existing nontrivial-relation branch is
retained. -/
def eval_permutationDataOfDecodedResolver_or_relation
    {shape : Shape} {G : Type*} [AddCommGroup G] [Module Fp G]
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    [DecidableEq G] [Inhabited G]
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments (instanceCommitment := instanceCommitment) urs hk vk ps ch)
      (x4BatchEvals (instanceCommitment := instanceCommitment) vk ps ch) a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch),
      OpenedMemberDecode (instanceCommitment := instanceCommitment)
        urs hk vk ps ch pbatch i hi)
    (hcount : deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch
      = (constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).sets.length)
    (hdup : hasDuplicateCommitmentPoint
      (assembleQueries vk instanceCommitment ps ch) = false)
    (hwf : permutationLastEvalsWellFormed ps = true)
    (hcoherent : PermutationChunkRoutingCoherent vk)
    (hbind : ∀
      (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)
      (point : Fp),
      point ∈ deployedSetPts (instanceCommitment := instanceCommitment) vk ps ch slot.setIndex →
      (decodedMemberPolynomial (instanceCommitment := instanceCommitment)
          urs hk vk ps ch memberDecode slot).eval point
          = deployedMemberClaim (instanceCommitment := instanceCommitment)
              vk ps ch slot point
        ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w)
    (p : Fin shape.numProofs) :
    let route := assembledQueryMemberRoute (instanceCommitment := instanceCommitment)
      vk ps ch hcount hdup
    let poly := decodedPolynomialResolver (instanceCommitment := instanceCommitment)
      urs hk vk ps ch memberDecode route
    ((permutationSetsOfResolver vk poly p).map
          (PermSetEval.map fun q => q.eval ch.x) = subProofPermSets ps p
      ∧ (permutationChunksOfResolver vk poly p).map (fun chunk =>
          (chunk.1.map fun q => q.eval ch.x,
            chunk.2.map fun pair => (pair.1.eval ch.x, pair.2.eval ch.x)))
        = subProofPermChunks vk ps p)
      ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  dsimp only
  refine bindOrRelationWitness
    (decodedPolynomialResolver_opens_or_relation
      (instanceCommitment := instanceCommitment)
      urs hk vk ps ch memberDecode
      (assembledQueryMemberRoute (instanceCommitment := instanceCommitment)
        vk ps ch hcount hdup)
      (assembleQueries vk instanceCommitment ps ch)
      (fun q hq => assembledQueryMemberRoute_faithful
        (instanceCommitment := instanceCommitment) vk ps ch hcount hdup q hq)
      hbind) fun hopen => ?_
  exact
    ⟨eval_permutationSetsOfResolver vk instanceCommitment ps ch _ hwf p hopen,
     eval_permutationChunksOfResolver
      vk instanceCommitment ps ch _ hwf hcoherent p hopen⟩

end Zcash.Snark
