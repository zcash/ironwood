import Zcash.Snark.Soundness.FiatShamir.Adversary.Algebraic

/-!
# Multiopen assembly provenance

Every point appended by the deployed multiopen MSM comes from the proof or verifying key.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

/-- The first component of a zipped pair is a member of the first list. -/
private theorem mem_of_mem_zip_fst {α β : Type*} {a : α} {b : β}
    {l₁ : List α} {l₂ : List β} (h : (a, b) ∈ l₁.zip l₂) : a ∈ l₁ := by
  induction l₁ generalizing l₂ with
  | nil => simp [List.zip_nil_left] at h
  | cons c l₁ ih =>
      cases l₂ with
      | nil => simp [List.zip_nil_right] at h
      | cons d l₂ =>
          rw [List.zip_cons_cons, List.mem_cons] at h
          rcases h with h | h
          · rw [Prod.mk.injEq] at h
            exact h.1 ▸ List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih h)

section MsmPoints

variable {k : ℕ} {F G : Type*}

-- `Msm` lives in `Zcash.Arithmetic`, so these accessors have to be declared into its own
-- namespace (`_root_.`) for generalized field notation to find them.

/-- The group points an MSM's appended terms reference. -/
def _root_.Zcash.Arithmetic.Msm.otherPoints (m : Msm k F G) : List G := m.other.map Prod.snd

theorem _root_.Zcash.Arithmetic.Msm.otherPoints_zero [Zero F] :
    (Msm.zero k F G).otherPoints = [] := rfl

theorem _root_.Zcash.Arithmetic.Msm.otherPoints_appendTerm (c : F) (P : G) (m : Msm k F G) :
    (m.appendTerm c P).otherPoints = P :: m.otherPoints := rfl

theorem _root_.Zcash.Arithmetic.Msm.otherPoints_scale [Mul F] (c : F) (m : Msm k F G) :
    (m.scale c).otherPoints = m.otherPoints := by
  simp [Msm.otherPoints, Msm.scale, List.map_map, Function.comp_def]

theorem _root_.Zcash.Arithmetic.Msm.otherPoints_add [Add F] (m₁ m₂ : Msm k F G) :
    (m₁.add m₂).otherPoints = m₁.otherPoints ++ m₂.otherPoints := by
  simp [Msm.otherPoints, Msm.add]

/-- The group points a commitment reference contributes. -/
def CommitmentRef.points : CommitmentRef k F G → List G
  | .point p => [p]
  | .msm m => m.otherPoints

end MsmPoints

section FoldProvenance

variable {k : ℕ} {F G : Type*} [Field F]

/-- The folded `h` commitment's points are its pieces. -/
theorem mem_otherPoints_vanishingHCommitment (xn : F) (hPieces : List G) :
    ∀ x ∈ (vanishingHCommitment k xn hPieces).otherPoints, x ∈ hPieces := by
  suffices h : ∀ (l : List G) (init : Msm k F G),
      ∀ x ∈ (l.foldl (fun acc c => (acc.scale xn).appendTerm 1 c) init).otherPoints,
        x ∈ init.otherPoints ∨ x ∈ l by
    intro x hx
    rcases h hPieces.reverse (Msm.zero k F G) x hx with h0 | hl
    · rw [Msm.otherPoints_zero] at h0
      exact absurd h0 (List.not_mem_nil)
    · exact List.mem_reverse.mp hl
  intro l
  induction l with
  | nil => exact fun init x hx => Or.inl hx
  | cons c l ih =>
      intro init x hx
      rcases ih ((init.scale xn).appendTerm 1 c) x hx with h0 | hl
      · rw [Msm.otherPoints_appendTerm, Msm.otherPoints_scale] at h0
        rcases List.mem_cons.mp h0 with rfl | h0
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl h0
      · exact Or.inr (List.mem_cons_of_mem _ hl)

/-- Accumulating one reference appends only its own points. -/
theorem mem_otherPoints_accumulateCommitment (pow : F) (c : CommitmentRef k F G)
    (acc : Msm k F G) :
    ∀ x ∈ (accumulateCommitment pow c acc).otherPoints,
      x ∈ c.points ∨ x ∈ acc.otherPoints := by
  intro x hx
  cases c with
  | point p =>
      simp only [accumulateCommitment, Msm.otherPoints_appendTerm] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl (List.mem_singleton_self _)
      · exact Or.inr hx
  | msm m =>
      simp only [accumulateCommitment, Msm.otherPoints_add, Msm.otherPoints_scale] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inr hx
      · exact Or.inl hx

/-- The compression fold appends only the set's referenced points. -/
theorem mem_otherPoints_compressSet (x1 : F)
    (setQueries : List (CommitmentRef k F G × List F)) (numPoints : ℕ) :
    ∀ x ∈ (compressSet x1 setQueries numPoints).1.otherPoints,
      ∃ qc ∈ setQueries, x ∈ qc.1.points := by
  suffices h : ∀ (l : List (CommitmentRef k F G × List F)) (st : Msm k F G × List F × F),
      ∀ x ∈ (l.foldl (fun (st : Msm k F G × List F × F) qc =>
          (accumulateCommitment st.2.2 qc.1 st.1,
           (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
           st.2.2 * x1)) st).1.otherPoints,
        x ∈ st.1.otherPoints ∨ ∃ qc ∈ l, x ∈ qc.1.points by
    intro x hx
    rcases h setQueries (Msm.zero k F G, List.replicate numPoints (0 : F), (1 : F)) x hx
      with h0 | hl
    · rw [Msm.otherPoints_zero] at h0
      exact absurd h0 (List.not_mem_nil)
    · exact hl
  intro l
  induction l with
  | nil => exact fun st x hx => Or.inl hx
  | cons qc l ih =>
      intro st x hx
      rcases ih _ x hx with h0 | ⟨qc', hqc', hx'⟩
      · rcases mem_otherPoints_accumulateCommitment st.2.2 qc.1 st.1 x h0 with h1 | h1
        · exact Or.inr ⟨qc, List.mem_cons_self .., h1⟩
        · exact Or.inl h1
      · exact Or.inr ⟨qc', List.mem_cons_of_mem _ hqc', hx'⟩

/-- The `x₄` collapse appends only `q'`, the incoming points, and the compressed points. -/
theorem mem_otherPoints_multiopenCombine (x4 : F) (qPrime : G)
    (qCommitments : List (Msm k F G)) (u : List F) (msmEval : F) (incoming : Msm k F G) :
    ∀ x ∈ (multiopenCombine x4 qPrime qCommitments u msmEval incoming).1.otherPoints,
      x = qPrime ∨ x ∈ incoming.otherPoints ∨ ∃ m ∈ qCommitments, x ∈ m.otherPoints := by
  suffices h : ∀ (l : List (Msm k F G × F)) (st : Msm k F G × F),
      ∀ x ∈ (l.foldl (fun (st : Msm k F G × F) p =>
          ((st.1.scale x4).add p.1, st.2 * x4 + p.2)) st).1.otherPoints,
        x ∈ st.1.otherPoints ∨ ∃ p ∈ l, x ∈ p.1.otherPoints by
    intro x hx
    rcases h (qCommitments.zip u) (incoming.appendTerm 1 qPrime, msmEval) x hx
      with h0 | ⟨p, hp, hx'⟩
    · rw [Msm.otherPoints_appendTerm] at h0
      rcases List.mem_cons.mp h0 with rfl | h0
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr ⟨p.1, (mem_of_mem_zip_fst hp), hx'⟩)
  intro l
  induction l with
  | nil => exact fun st x hx => Or.inl hx
  | cons p l ih =>
      intro st x hx
      rcases ih _ x hx with h0 | ⟨p', hp', hx'⟩
      · rw [Msm.otherPoints_add, Msm.otherPoints_scale] at h0
        rcases List.mem_append.mp h0 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨p, List.mem_cons_self .., h1⟩
      · exact Or.inr ⟨p', List.mem_cons_of_mem _ hp', hx'⟩

end FoldProvenance

section GroupingProvenance

variable {k : ℕ} {F G : Type*} [DecidableEq F]

omit [DecidableEq F] in
private theorem mem_comms_foldl (queries : List (VerifierQuery k F G)) :
    ∀ (init : List (CommitmentId × CommitmentRef k F G)),
    ∀ ce ∈ queries.foldl (fun acc q =>
        if acc.any (fun c => decide (c.1 = q.commId)) then acc
        else acc ++ [(q.commId, q.commitment)]) init,
      ce ∈ init ∨ ∃ q ∈ queries, ce = (q.commId, q.commitment) := by
  induction queries with
  | nil => exact fun init ce hce => Or.inl hce
  | cons q queries ih =>
      intro init ce hce
      rw [List.foldl_cons] at hce
      rcases ih _ ce hce with h0 | ⟨q', hq', rfl⟩
      · split at h0
        · exact Or.inl h0
        · rcases List.mem_append.mp h0 with h1 | h1
          · exact Or.inl h1
          · rw [List.mem_singleton] at h1
            exact Or.inr ⟨q, List.mem_cons_self .., h1⟩
      · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', rfl⟩

/-- Grouping only reorganizes: every grouped reference is some query's commitment. -/
theorem constructIntermediateSets_ref_mem (queries : List (VerifierQuery k F G)) :
    ∀ s ∈ (constructIntermediateSets queries).sets, ∀ ce ∈ s,
      ∃ q ∈ queries, ce.1 = q.commitment := by
  intro s hs ce hce
  simp only [constructIntermediateSets] at hs
  obtain ⟨si, -, rfl⟩ := List.mem_map.mp hs
  obtain ⟨cd, hcd, rfl⟩ := List.mem_map.mp hce
  have hcd' := (List.mem_filter.mp hcd).1
  rw [List.mem_reverse] at hcd'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcd'
  rcases mem_comms_foldl queries [] c hc with h0 | ⟨q, hq, rfl⟩
  · exact absurd h0 (List.not_mem_nil)
  · exact ⟨q, hq, rfl⟩

end GroupingProvenance

section QueryProvenance

variable {shape : Shape} {F G : Type*} [Field F] [Inhabited G]

/-- Proof and verifying-key commitments that the deployed verifier may feed to multiopen. -/
def AssemblyPoint (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape F G) (x : G) : Prop :=
  (∃ (p : Fin shape.numProofs) (e : ℕ × ℤ), e ∈ vk.instanceQueryLayout
      ∧ x = instanceCommitment p e.1)
  ∨ (∃ (p : Fin shape.numProofs) (e : ℕ × ℤ), e ∈ vk.adviceQueryLayout
      ∧ x = finFnG (ps.adviceCommitments p) e.1)
  ∨ (∃ p s, x = ps.permutationProduct p s)
  ∨ (∃ p l, x = ps.lookupProduct p l)
  ∨ (∃ p l, x = ps.lookupPermutedInput p l)
  ∨ (∃ p l, x = ps.lookupPermutedTable p l)
  ∨ (∃ e : ℕ × ℤ, e ∈ vk.fixedQueryLayout ∧ x = vk.fixedCommitment e.1)
  ∨ (∃ c, x = vk.permutationCommonCommitment c)
  ∨ (∃ i, x = ps.hPieces i)
  ∨ x = ps.vanishingRandom
  ∨ x = ps.multiopenQPrime

omit [Inhabited G] in
private theorem columnQueries_commitment {k : ℕ} (omega x : F) (commitment : ℕ → G)
    (mkId : ℕ → CommitmentId) (layout : List (ℕ × ℤ)) (evals : List F) :
    ∀ q ∈ columnQueries (k := k) omega x commitment mkId layout evals,
      ∃ e ∈ layout, q.commitment = CommitmentRef.point (commitment e.1) := by
  intro q hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
  exact ⟨e.1, (mem_of_mem_zip_fst he), rfl⟩

omit [Inhabited G] in
private theorem permutationQueries_commitment {k : ℕ} (x xNext xLast : F)
    (mkId : ℕ → CommitmentId) (sets : List (G × PermSetEval F)) :
    ∀ q ∈ permutationQueries (k := k) x xNext xLast mkId sets,
      ∃ s ∈ sets, q.commitment = CommitmentRef.point s.1 := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨s, hs, hq2⟩ := List.mem_flatMap.mp h
    have hs1 : s.1 ∈ sets := (mem_of_mem_zip_fst hs)
    rcases List.mem_cons.mp hq2 with rfl | hq2
    · exact ⟨s.1, hs1, rfl⟩
    rcases List.mem_cons.mp hq2 with rfl | hq2
    · exact ⟨s.1, hs1, rfl⟩
    · exact absurd hq2 (List.not_mem_nil)
  · obtain ⟨s, hs, hq2⟩ := List.mem_filterMap.mp h
    obtain ⟨le, -, rfl⟩ := Option.map_eq_some_iff.mp hq2
    have hs1 : s.1 ∈ sets :=
      mem_of_mem_zip_fst (List.mem_reverse.mp (List.mem_of_mem_drop hs))
    exact ⟨s.1, hs1, rfl⟩

omit [Inhabited G] in
private theorem lookupQueries_commitment {k : ℕ} (x xInv xNext : F)
    (mkProduct mkInput mkTable : ℕ → CommitmentId)
    (lookups : List (LookupCommitments G × LookupEval F)) :
    ∀ q ∈ lookupQueries (k := k) x xInv xNext mkProduct mkInput mkTable lookups,
      ∃ l ∈ lookups, q.commitment = CommitmentRef.point l.1.product
        ∨ q.commitment = CommitmentRef.point l.1.permutedInput
        ∨ q.commitment = CommitmentRef.point l.1.permutedTable := by
  intro q hq
  obtain ⟨l, hl, hq2⟩ := List.mem_flatMap.mp hq
  have hl1 : l.1 ∈ lookups := (mem_of_mem_zip_fst hl)
  refine ⟨l.1, hl1, ?_⟩
  rcases List.mem_cons.mp hq2 with rfl | hq2
  · exact Or.inl rfl
  rcases List.mem_cons.mp hq2 with rfl | hq2
  · exact Or.inr (Or.inl rfl)
  rcases List.mem_cons.mp hq2 with rfl | hq2
  · exact Or.inr (Or.inr rfl)
  rcases List.mem_cons.mp hq2 with rfl | hq2
  · exact Or.inr (Or.inl rfl)
  rcases List.mem_cons.mp hq2 with rfl | hq2
  · exact Or.inl rfl
  · exact absurd hq2 (List.not_mem_nil)

omit [Inhabited G] in
private theorem permutationCommonQueries_commitment {k : ℕ} (x : F)
    (mkId : ℕ → CommitmentId) (commsEvals : List (G × F)) :
    ∀ q ∈ permutationCommonQueries (k := k) x mkId commsEvals,
      ∃ ce ∈ commsEvals, q.commitment = CommitmentRef.point ce.1 := by
  intro q hq
  obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hq
  exact ⟨ce.1, (mem_of_mem_zip_fst hce), rfl⟩

/-- Every query's commitment points lie in the assembly pool. -/
theorem assembleQueries_points_mem (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) :
    ∀ q ∈ assembleQueries vk instanceCommitment ps ch, ∀ x ∈ q.commitment.points,
      AssemblyPoint vk instanceCommitment ps x := by
  intro q hq x hx
  simp only [assembleQueries] at hq
  rcases List.mem_append.mp hq with hq | hq
  · -- per-proof, fixed, and common blocks
    rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · -- per-proof block
        obtain ⟨qs, hqs, hq⟩ := List.mem_flatten.mp hq
        obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hqs
        rcases List.mem_append.mp hq with hq | hq
        · rcases List.mem_append.mp hq with hq | hq
          · rcases List.mem_append.mp hq with hq | hq
            · -- instance columns
              obtain ⟨e, he, hcq⟩ := columnQueries_commitment _ _ _ _ _ _ q hq
              rw [hcq] at hx
              simp only [CommitmentRef.points, List.mem_singleton] at hx
              exact Or.inl ⟨p, e, he, hx⟩
            · -- advice columns
              obtain ⟨e, he, hcq⟩ := columnQueries_commitment _ _ _ _ _ _ q hq
              rw [hcq] at hx
              simp only [CommitmentRef.points, List.mem_singleton] at hx
              exact Or.inr (Or.inl ⟨p, e, he, hx⟩)
          · -- permutation products
            obtain ⟨s, hs, hcq⟩ := permutationQueries_commitment _ _ _ _ _ q hq
            obtain ⟨si, rfl⟩ := List.mem_ofFn.mp hs
            rw [hcq] at hx
            simp only [CommitmentRef.points, List.mem_singleton] at hx
            exact Or.inr (Or.inr (Or.inl ⟨p, si, hx⟩))
        · -- lookups
          obtain ⟨l, hl, hcq⟩ := lookupQueries_commitment _ _ _ _ _ _ _ q hq
          obtain ⟨li, rfl⟩ := List.mem_ofFn.mp hl
          rcases hcq with hcq | hcq | hcq <;> rw [hcq] at hx <;>
            simp only [CommitmentRef.points, List.mem_singleton] at hx
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, li, hx⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, li, hx⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, li, hx⟩)))))
      · -- fixed columns
        obtain ⟨e, he, hcq⟩ := columnQueries_commitment _ _ _ _ _ _ q hq
        rw [hcq] at hx
        simp only [CommitmentRef.points, List.mem_singleton] at hx
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, hx⟩))))))
    · -- permutation common
      obtain ⟨ce, hce, hcq⟩ := permutationCommonQueries_commitment _ _ _ q hq
      obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hce
      rw [hcq] at hx
      simp only [CommitmentRef.points, List.mem_singleton] at hx
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨c, hx⟩)))))))
  · -- vanishing block
    rcases List.mem_cons.mp hq with rfl | hq
    · -- the folded h commitment
      have hx' := mem_otherPoints_vanishingHCommitment _ _ x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx'
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨i, rfl⟩))))))))
    rcases List.mem_cons.mp hq with rfl | hq
    · -- the random poly commitment
      simp only [CommitmentRef.points, List.mem_singleton] at hx
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hx)))))))))
    · exact absurd hq (List.not_mem_nil)

end QueryProvenance

section MultiopenProvenance

local instance : Inhabited VestaG := ⟨0⟩

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}

/-- Every point appended by the deployed multiopen MSM is `q'` or an `AssemblyPoint`. -/
theorem multiopenMsm_points_mem (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp) :
    ∀ x ∈ (multiopenMsm vk instanceCommitment ps ch).otherPoints,
      x = ps.multiopenQPrime ∨ AssemblyPoint vk instanceCommitment ps x := by
  intro x hx
  -- `multiopenMsm` is `(assembleOpening …).1`; peel the `x₄` collapse
  have hopen : multiopenMsm vk instanceCommitment ps ch
      = (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
          (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) (Msm.zero shape.k Fp VestaG)).1 :=
    rfl
  rw [hopen, assembleOpening] at hx
  set grouped := constructIntermediateSets (assembleQueries vk instanceCommitment ps ch) with hg
  rcases mem_otherPoints_multiopenCombine _ _ _ _ _ _ x hx with hq | hinc | ⟨m, hm, hxm⟩
  · exact Or.inl hq
  · rw [Msm.otherPoints_zero] at hinc
    exact absurd hinc (List.not_mem_nil)
  · -- `m` is one point set's compressed commitment
    obtain ⟨cmp, hcmp, rfl⟩ := List.mem_map.mp hm
    obtain ⟨sp, hsp, rfl⟩ := List.mem_map.mp hcmp
    obtain ⟨qc, hqc, hxc⟩ := mem_otherPoints_compressSet _ _ _ x hxm
    -- `qc.1` is a grouped commitment reference; trace it to a query
    have hsp1 : sp.1 ∈ grouped.sets :=
      mem_of_mem_zip_fst hsp
    obtain ⟨q, hq, hqcomm⟩ := constructIntermediateSets_ref_mem _ sp.1 hsp1 qc hqc
    refine Or.inr (assembleQueries_points_mem vk instanceCommitment ps ch q hq x ?_)
    rw [← hqcomm]
    exact hxc

/-- A list representing `q'` and every `AssemblyPoint` covers every point appended by multiopen. -/
theorem multiopenMsm_points_covered (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (aps : AlgebraicProofString shape basis) (ν : Fin 11 → Fp)
    (L : List (AlgebraicPoint (F := Fp) basis))
    (hL : ∀ x, (x = aps.erase.multiopenQPrime ∨ AssemblyPoint vk instanceCommitment aps.erase x) →
      ∃ ap ∈ L, ap.point = x) :
    ∀ pr ∈ (multiopenMsm vk instanceCommitment aps.erase (chRecord ν (fun _ => 0))).other,
      ∃ ap ∈ L, ap.point = pr.2 := by
  intro pr hpr
  have hx : pr.2 ∈ (multiopenMsm vk instanceCommitment aps.erase (chRecord ν (fun _ => 0))).otherPoints :=
    List.mem_map_of_mem hpr
  exact hL pr.2 (multiopenMsm_points_mem vk instanceCommitment aps.erase (chRecord ν (fun _ => 0)) pr.2 hx)

/-- Build `AlgebraicWfProof` from representations of `q'`, the proof commitments, and the
verifying-key commitments. -/
def AlgebraicWfProof.ofStandard {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase)
    (L : List (AlgebraicPoint (F := Fp) basis))
    (hL : ∀ x, (x = aps.erase.multiopenQPrime ∨ AssemblyPoint vk instanceCommitment aps.erase x) →
      ∃ ap ∈ L, ap.point = x) :
    AlgebraicWfProof basis vk instanceCommitment :=
  AlgebraicWfProof.ofRepresented aps hwf (fun ν =>
    RepresentedMultiopen.ofCoveredList vk instanceCommitment aps.erase ν L
      (multiopenMsm_points_covered vk instanceCommitment aps ν L hL))

end MultiopenProvenance

end Zcash.Snark
