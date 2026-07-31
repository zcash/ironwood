import Zcash.Snark.Soundness.Multiopen.ValueCheckDeployed

/-!
# The action-dependent budget, capped at the consensus maximum

The joint accept floor of the budgeted member extraction is a sum of four thresholds whose counts
— set-member counts, the `x₄` pair count, the point-union size — grow with the number of bundle
actions (`shape.numProofs`). This module bounds them all by shape-level quantities: a query
budget linear in the action count, and the point-set arity. The resulting `actionBudget` is
monotone in the action count, so consensus's `numProofs ≤ 2¹⁶ − 1` caps it at the
consensus-maximum shape — the action-dependent term the composite bound consumes.
-/

namespace Zcash.Snark

open scoped ENNReal

/-- The shape-level query budget: one opening query per layout entry, three permutation openings
per set, five per lookup, the shared fixed and σ columns, and the two vanishing queries. -/
def queryBudget (shape : Shape) : ℕ :=
  shape.numProofs * (shape.numInstanceQueries + shape.numAdviceQueries
    + 3 * shape.numPermutationSets + 5 * shape.numLookups)
  + shape.numFixedQueries + shape.numPermutationColumns + 2

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- A `flatMap` with `c`-bounded outputs has length at most `c` per element. -/
private theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (c : ℕ)
    (hf : ∀ a, (f a).length ≤ c) : (l.flatMap f).length ≤ c * l.length := by
  rw [List.length_flatMap]
  refine le_trans (List.sum_le_card_nsmul _ c ?_) ?_
  · intro n hn
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hn
    exact hf a
  · rw [List.length_map, smul_eq_mul, mul_comm]

/-- A flattened `ofFn` with `c`-bounded entries has length at most `n · c`. -/
private theorem length_flatten_ofFn_le {α : Type*} {n : ℕ} (f : Fin n → List α) (c : ℕ)
    (hf : ∀ i, (f i).length ≤ c) : ((List.ofFn f).flatten).length ≤ n * c := by
  rw [List.length_flatten]
  refine le_trans (List.sum_le_card_nsmul _ c ?_) ?_
  · intro m hm
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact hf i
  · rw [List.length_map, List.length_ofFn, smul_eq_mul]

/-- A column family contributes at most one query per claimed evaluation. -/
private theorem columnQueries_length_le {k' : ℕ} {F' G' : Type*} [Field F'] (omega x : F')
    (commitment : ℕ → G') (mkId : ℕ → CommitmentId) (layout : List (ℕ × ℤ))
    (evals : List F') :
    (columnQueries (k := k') omega x commitment mkId layout evals).length ≤ evals.length := by
  rw [columnQueries, List.length_map, List.length_zip]
  exact min_le_right _ _

/-- The permutation section contributes at most three queries per set. -/
private theorem permutationQueries_length_le {k' : ℕ} {F' G' : Type*} [Field F']
    (x xNext xLast : F') (mkId : ℕ → CommitmentId) (sets : List (G' × PermSetEval F')) :
    (permutationQueries (k := k') x xNext xLast mkId sets).length ≤ 3 * sets.length := by
  rw [permutationQueries, List.length_append]
  have hzip : (sets.zip (List.range sets.length)).length = sets.length := by
    rw [List.length_zip, List.length_range, min_self]
  refine le_trans (Nat.add_le_add
    (length_flatMap_le _ _ 2 (fun s => le_of_eq rfl))
    (le_trans (List.length_filterMap_le _ _)
      (by rw [List.length_drop, List.length_reverse]))) ?_
  rw [hzip]
  omega

/-- The lookup section contributes five queries per lookup. -/
private theorem lookupQueries_length_le {k' : ℕ} {F' G' : Type*} [Field F']
    (x xInv xNext : F') (mkProduct mkInput mkTable : ℕ → CommitmentId)
    (lookups : List (LookupCommitments G' × LookupEval F')) :
    (lookupQueries (k := k') x xInv xNext mkProduct mkInput mkTable lookups).length
      ≤ 5 * lookups.length := by
  rw [lookupQueries]
  have hzip : (lookups.zip (List.range lookups.length)).length = lookups.length := by
    rw [List.length_zip, List.length_range, min_self]
  refine le_trans (length_flatMap_le _ _ 5 (fun l => le_of_eq rfl)) ?_
  rw [hzip]

/-- The σ section contributes one query per common column. -/
private theorem permutationCommonQueries_length_le {k' : ℕ} {F' G' : Type*} [Field F']
    (x : F') (mkId : ℕ → CommitmentId) (commsEvals : List (G' × F')) :
    (permutationCommonQueries (k := k') x mkId commsEvals).length ≤ commsEvals.length := by
  rw [permutationCommonQueries, List.length_map, List.length_zip, List.length_range, min_self]

omit [AddCommGroup G] [Module Fp G] in
/-- **The deployed query list fits the shape budget.** -/
theorem assembleQueries_length_le [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) :
    (assembleQueries vk instanceCommitment ps ch).length ≤ queryBudget shape := by
  simp only [assembleQueries, List.length_append]
  refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (length_flatten_ofFn_le _ (shape.numInstanceQueries + shape.numAdviceQueries
      + 3 * shape.numPermutationSets + 5 * shape.numLookups) (fun p => ?_))
    (le_trans (columnQueries_length_le (k' := shape.k) vk.omega ch.x vk.fixedCommitment
      CommitmentId.fixedCol vk.fixedQueryLayout (List.ofFn ps.fixedEvals))
      (le_of_eq (List.length_ofFn ..))))
    (le_trans (permutationCommonQueries_length_le (k' := shape.k) ch.x CommitmentId.permCommon
      (List.ofFn (fun c => (vk.permutationCommonCommitment c, ps.permutationCommonEvals c))))
      (le_of_eq (List.length_ofFn ..))))
    (show (vanishingQueries (k := shape.k) ch.x
        (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces))
        (expectedHEval (allExpressions vk ps ch
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2) ch.y
          (ch.x ^ vk.n))
        ps.vanishingRandom ps.vanishingRandomEval).length ≤ 2 from le_of_eq rfl)) ?_
  · simp only [List.length_append]
    have h1 := columnQueries_length_le (k' := shape.k) vk.omega ch.x
      (instanceCommitment p) (CommitmentId.instanceCol p) vk.instanceQueryLayout
      (List.ofFn (ps.instanceEvals p))
    have h2 := columnQueries_length_le (k' := shape.k) vk.omega ch.x
      (finFnG (ps.adviceCommitments p)) (CommitmentId.adviceCol p) vk.adviceQueryLayout
      (List.ofFn (ps.adviceEvals p))
    have h3 := permutationQueries_length_le (k' := shape.k) ch.x
      (rotateOmega vk.omega ch.x 1)
      (rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1)))
      (CommitmentId.permProduct p)
      (List.ofFn (fun s => (ps.permutationProduct p s, ps.permutationSetEvals p s)))
    have h4 := lookupQueries_length_le (k' := shape.k) ch.x
      (rotateOmega vk.omega ch.x (-1)) (rotateOmega vk.omega ch.x 1)
      (CommitmentId.lookupProduct p) (CommitmentId.lookupPermInput p)
      (CommitmentId.lookupPermTable p) (List.ofFn (fun l =>
      (LookupCommitments.mk (ps.lookupProduct p l) (ps.lookupPermutedInput p l)
        (ps.lookupPermutedTable p l), ps.lookupEvals p l)))
    simp only [List.length_ofFn] at h1 h2 h3 h4
    omega
  · rw [queryBudget]

/-! ## Structural bounds on the deployed counts -/

omit [AddCommGroup G] [Module Fp G] in
/-- The deployed `x4` pair count is at most the shape's point-set arity. -/
theorem deployedX4PairCount_le_numPointSets [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs -> Nat -> G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    deployedX4PairCount vk instanceCommitment ps ch <= shape.numPointSets := by
  simp only [deployedX4PairCount, deployedX4Pairs, List.length_zip, List.length_ofFn]
  exact min_le_right _ _

/-- Members of the first-appearance point fold are opening points of the folded queries. -/
private theorem mem_dedup_points_foldl {k : Nat} {F G' : Type*} [DecidableEq F] :
    forall (queries : List (VerifierQuery k F G')) (init : List F) (x : F),
      x ∈ queries.foldl (fun acc q => if q.point ∈ acc then acc else acc ++ [q.point]) init ->
      x ∈ init ∨ ∃ q ∈ queries, q.point = x := by
  intro queries
  induction queries with
  | nil =>
      intro init x hx
      exact Or.inl hx
  | cons q rest ih =>
      intro init x hx
      rw [List.foldl_cons] at hx
      rcases ih _ x hx with hin | ⟨q', hq', hpt⟩
      · by_cases hq : q.point ∈ init
        · rw [if_pos hq] at hin
          exact Or.inl hin
        · rw [if_neg hq] at hin
          rcases List.mem_append.mp hin with h | h
          · exact Or.inl h
          · exact Or.inr ⟨q, List.mem_cons_self .., (List.mem_singleton.mp h).symm⟩
      · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', hpt⟩

/-- Every point in a grouped point set is some query's opening point. -/
theorem constructIntermediateSets_points_getD_mem_queries
    {k : Nat} {F G' : Type*} [DecidableEq F] [DecidableEq G']
    (queries : List (VerifierQuery k F G')) (si : Nat) {x : F}
    (hx : x ∈ (constructIntermediateSets queries).points.getD si []) :
    ∃ q ∈ queries, q.point = x := by
  classical
  have key : ∀ pl ∈ (constructIntermediateSets queries).points, x ∈ pl ->
      ∃ q ∈ queries, q.point = x := by
    intro pl hpl hxpl
    simp only [constructIntermediateSets] at hpl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hpl
    obtain ⟨i, hi, hix⟩ := List.mem_filterMap.mp hxpl
    rw [List.getElem?_eq_some_iff] at hix
    obtain ⟨hilt, rfl⟩ := hix
    rcases mem_dedup_points_foldl queries [] _ (List.getElem_mem hilt) with h0 | h
    · exact absurd h0 List.not_mem_nil
    · exact h
  rcases lt_or_ge si (constructIntermediateSets queries).points.length with hlt | hge
  · rw [List.getD_eq_getElem _ _ hlt] at hx
    exact key _ (List.getElem_mem hlt) hx
  · rw [List.getD_eq_default _ _ hge] at hx
    exact absurd hx List.not_mem_nil

omit [AddCommGroup G] [Module Fp G] in
/-- The deployed point union has at most as many points as the verifier has opening queries. -/
theorem deployedAllPts_card_le [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs -> Nat -> G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    (deployedAllPts vk instanceCommitment ps ch).card <=
      (assembleQueries vk instanceCommitment ps ch).length := by
  classical
  have hsub : deployedAllPts vk instanceCommitment ps ch <=
      ((assembleQueries vk instanceCommitment ps ch).map (·.point)).toFinset := by
    intro x hx
    rw [deployedAllPts, Finset.mem_biUnion] at hx
    obtain ⟨j, -, hj⟩ := hx
    rw [deployedSetPts, List.mem_toFinset] at hj
    obtain ⟨q, hq, hqx⟩ := constructIntermediateSets_points_getD_mem_queries _ j hj
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨q, hq, hqx⟩
  calc
    (deployedAllPts vk instanceCommitment ps ch).card
        <= ((assembleQueries vk instanceCommitment ps ch).map (·.point)).toFinset.card :=
      Finset.card_le_card hsub
    _ <= ((assembleQueries vk instanceCommitment ps ch).map (·.point)).length :=
      List.toFinset_card_le _
    _ = (assembleQueries vk instanceCommitment ps ch).length := List.length_map ..

omit [AddCommGroup G] [Module Fp G] in
/-- Each point set's member count fits the shape budget. -/
theorem deployedSetQueries_length_le [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (i : ℕ) :
    (deployedSetQueries vk instanceCommitment ps ch i).length ≤ queryBudget shape := by
  refine le_trans ?_ (le_trans
    (constructIntermediateSets_sets_getD_length_le (assembleQueries vk instanceCommitment ps ch) i)
    (assembleQueries_length_le vk instanceCommitment ps ch))
  show (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.zip
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points).getD i
        ([], [])).1.length ≤ _
  rw [constructIntermediateSets_zip_sets_getD]

omit [AddCommGroup G] [Module Fp G] in
/-- The point union fits the shape budget. -/
theorem deployedAllPts_card_le_budget [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) :
    (deployedAllPts vk instanceCommitment ps ch).card ≤ queryBudget shape :=
  le_trans (deployedAllPts_card_le vk instanceCommitment ps ch) (assembleQueries_length_le vk instanceCommitment ps ch)

/-! ## The action-dependent budget -/

/-- **The action-dependent budget.** The four squeeze thresholds of the joint accept floor, each
count replaced by its shape-level bound: set members and point unions by the query budget, the
`x₄` pair count by the point-set arity. -/
noncomputable def actionBudget (shape : Shape) (k' : ℕ) : ℝ≥0∞ :=
  (queryBudget shape : ℝ≥0∞) / Fintype.card Fp
  + ((shape.numPointSets : ℝ≥0∞) / Fintype.card Fp
    + ((max (2 ^ k') (queryBudget shape) + queryBudget shape + queryBudget shape : ℕ) : ℝ≥0∞)
        / Fintype.card Fp
    + (shape.numPointSets : ℝ≥0∞) / Fintype.card Fp)

omit [AddCommGroup G] [Module Fp G] in
/-- **The joint accept floor's threshold fits the action budget**, for every proof string,
challenge record, and point set. The uniform worst case the resampled-joint threshold consumes. -/
theorem deployed_member_threshold_le_actionBudget [Inhabited G] {shape : Shape}
    (urs : URS G) (_hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (i : ℕ) :
    (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
      + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
      ≤ actionBudget shape urs.k := by
  rw [actionBudget]
  have hL : (deployedSetQueries vk instanceCommitment ps ch i).length - 1 ≤ queryBudget shape :=
    le_trans (Nat.sub_le _ _) (deployedSetQueries_length_le vk instanceCommitment ps ch i)
  have hC : deployedX4PairCount vk instanceCommitment ps ch - 1 ≤ shape.numPointSets :=
    le_trans (Nat.sub_le _ _) (deployedX4PairCount_le_numPointSets vk instanceCommitment ps ch)
  have hC' : deployedX4PairCount vk instanceCommitment ps ch ≤ shape.numPointSets :=
    deployedX4PairCount_le_numPointSets vk instanceCommitment ps ch
  have hP := deployedAllPts_card_le_budget vk instanceCommitment ps ch
  have hmid : max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
      + (deployedAllPts vk instanceCommitment ps ch).card + (deployedAllPts vk instanceCommitment ps ch).card
      ≤ max (2 ^ urs.k) (queryBudget shape) + queryBudget shape + queryBudget shape := by
    have hmax : max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
        ≤ max (2 ^ urs.k) (queryBudget shape) := max_le_max le_rfl hP
    omega
  gcongr

/-- The query budget is monotone in the action count. -/
theorem queryBudget_mono {shape shape' : Shape}
    (hnp : shape.numProofs ≤ shape'.numProofs)
    (hiq : shape.numInstanceQueries = shape'.numInstanceQueries)
    (haq : shape.numAdviceQueries = shape'.numAdviceQueries)
    (hps : shape.numPermutationSets = shape'.numPermutationSets)
    (hlk : shape.numLookups = shape'.numLookups)
    (hfq : shape.numFixedQueries = shape'.numFixedQueries)
    (hpc : shape.numPermutationColumns = shape'.numPermutationColumns) :
    queryBudget shape ≤ queryBudget shape' := by
  rw [queryBudget, queryBudget, hiq, haq, hps, hlk, hfq, hpc]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ hnp) _) _) _

/-- **The consensus-maximum cap.** With the circuit constants shared and the action count within
consensus's `2¹⁶ − 1`, the action budget is capped by its value at the consensus-maximum
shape — the term the composite bound consumes for every deployable bundle. -/
theorem actionBudget_le_consensusMax {shape shape' : Shape} (k' : ℕ)
    (hnp : shape.numProofs ≤ shape'.numProofs)
    (_hcap : shape'.numProofs = 2 ^ 16 - 1)
    (hiq : shape.numInstanceQueries = shape'.numInstanceQueries)
    (haq : shape.numAdviceQueries = shape'.numAdviceQueries)
    (hps : shape.numPermutationSets = shape'.numPermutationSets)
    (hlk : shape.numLookups = shape'.numLookups)
    (hfq : shape.numFixedQueries = shape'.numFixedQueries)
    (hpc : shape.numPermutationColumns = shape'.numPermutationColumns)
    (hpts : shape.numPointSets ≤ shape'.numPointSets) :
    actionBudget shape k' ≤ actionBudget shape' k' := by
  have hqb := queryBudget_mono hnp hiq haq hps hlk hfq hpc
  rw [actionBudget, actionBudget]
  have hmid : max (2 ^ k') (queryBudget shape) + queryBudget shape + queryBudget shape
      ≤ max (2 ^ k') (queryBudget shape') + queryBudget shape' + queryBudget shape' := by
    have hmax : max (2 ^ k') (queryBudget shape) ≤ max (2 ^ k') (queryBudget shape') :=
      max_le_max le_rfl hqb
    omega
  gcongr

end Zcash.Snark
