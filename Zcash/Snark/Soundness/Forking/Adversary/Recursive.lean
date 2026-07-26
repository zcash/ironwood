import Zcash.Snark.Soundness.AGM.Prover
import Zcash.Snark.Soundness.Forking.Adversary.Adaptive
import Mathlib.Data.Fintype.Perm

/-!
# Executable recursive Fiat–Shamir forking

Rerun an oracle adversary under one-point reprogramming to compute a ternary algebraic fork
certificate from a finite tape.
-/

namespace Zcash.Snark

/-- Extractor randomness: `order` lists replacement challenges, and `child u` supplies fresh
randomness below challenge `u`. -/
inductive RecursiveForkCoins (F : Type*) : ℕ → Type _ where
  | leaf : RecursiveForkCoins F 0
  | node {d : ℕ} (order : List F) (child : F → RecursiveForkCoins F d) :
      RecursiveForkCoins F (d + 1)

/-- Finite random tape for the extractor. Each node contains a uniformly sampled permutation of
the challenge set and independent child tapes. -/
inductive RecursiveForkTape (F : Type*) [Fintype F] : ℕ → Type _ where
  | leaf : RecursiveForkTape F 0
  | node {d : ℕ} (order : Fin (Fintype.card F) ≃ F)
      (child : F → RecursiveForkTape F d) :
      RecursiveForkTape F (d + 1)

namespace RecursiveForkTape

/-- The permutation written as a complete sampling-without-replacement order. -/
def orderList {F : Type*} [Fintype F]
    (order : Fin (Fintype.card F) ≃ F) : List F :=
  List.ofFn order

/-- Erase the finite tape wrapper to the executable extractor's coin format. -/
def toCoins {F : Type*} [Fintype F] :
    {d : ℕ} → RecursiveForkTape F d → RecursiveForkCoins F d
  | 0, .leaf => .leaf
  | _ + 1, .node order child =>
      .node (orderList order) (fun u => (child u).toCoins)

/-- A tape node tries every challenge exactly once. -/
theorem orderList_nodup {F : Type*} [Fintype F]
    (order : Fin (Fintype.card F) ≃ F) :
    (orderList order).Nodup := by
  exact List.nodup_ofFn.mpr order.injective

/-- Every challenge occurs in a tape node's sampling order. -/
theorem mem_orderList {F : Type*} [Fintype F]
    (order : Fin (Fintype.card F) ≃ F) (u : F) : u ∈ orderList order := by
  rw [orderList, List.mem_ofFn]
  exact ⟨order.symm u, order.apply_symm_apply u⟩

/-- Depth-zero tapes contain no randomness. -/
def equivZero {F : Type*} [Fintype F] : RecursiveForkTape F 0 ≃ Unit where
  toFun := fun | .leaf => ()
  invFun := fun _ => .leaf
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x; rfl

/-- A positive-depth tape is one challenge order and one child tape per challenge. -/
def equivSucc {F : Type*} [Fintype F] (d : ℕ) :
    RecursiveForkTape F (d + 1) ≃
      ((Fin (Fintype.card F) ≃ F) × (F → RecursiveForkTape F d)) where
  toFun := fun | .node order child => (order, child)
  invFun := fun p => .node p.1 p.2
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x; rfl

/-- The finite tape space sampled by the extractor probability experiment. -/
instance instFintype {F : Type*} [Fintype F] [DecidableEq F] :
    (d : ℕ) → Fintype (RecursiveForkTape F d)
  | 0 => Fintype.ofEquiv Unit equivZero.symm
  | d + 1 =>
      letI := instFintype (F := F) d
      Fintype.ofEquiv
        ((Fin (Fintype.card F) ≃ F) × (F → RecursiveForkTape F d))
        (equivSucc d).symm

/-- The uniformly sampled finite tape space is nonempty. -/
noncomputable instance instNonempty {F : Type*} [Fintype F] [DecidableEq F] :
    (d : ℕ) → Nonempty (RecursiveForkTape F d)
  | 0 => ⟨.leaf⟩
  | d + 1 => by
      let child : RecursiveForkTape F d := Classical.choice (instNonempty (F := F) d)
      exact ⟨.node (Fintype.equivFin F).symm (fun _ => child)⟩

end RecursiveForkTape

/-- The node reached after following a list of already-fixed challenges through extractor coins. -/
structure RecursiveForkNode (F : Type*) where
  depth : ℕ
  order : List F
  child : F → RecursiveForkCoins F depth

namespace RecursiveForkCoins

/-- Every node scans the complete challenge set, and all child tapes are complete recursively. -/
def Complete {F : Type*} [Fintype F] : {d : ℕ} → RecursiveForkCoins F d → Prop
  | 0, .leaf => True
  | _ + 1, .node order child => (∀ u : F, u ∈ order) ∧ ∀ u, Complete (child u)

/-- Every node tries at most `n` challenges, recursively. -/
def Bounded {F : Type*} (n : ℕ) : {d : ℕ} → RecursiveForkCoins F d → Prop
  | 0, .leaf => True
  | _ + 1, .node order child => order.length ≤ n ∧ ∀ u, Bounded n (child u)

/-- Follow previously fixed challenges to the next extractor node. -/
def nodeAt {F : Type*} : {d : ℕ} → RecursiveForkCoins F d → List F →
    Option (RecursiveForkNode F)
  | 0, .leaf, _ => none
  | _ + 1, .node order child, [] => some ⟨_, order, child⟩
  | _ + 1, .node _ child, u :: us => nodeAt (child u) us

@[simp] theorem nodeAt_nil {F : Type*} {d : ℕ} (order : List F)
    (child : F → RecursiveForkCoins F d) :
    nodeAt (.node order child) [] = some ⟨d, order, child⟩ := rfl

theorem nodeAt_append_singleton {F : Type*} {k d : ℕ} (root : RecursiveForkCoins F k)
    (path : List F) (u : F) (order : List F) (child : F → RecursiveForkCoins F d)
    (h : root.nodeAt path = some ⟨d, order, child⟩) :
    root.nodeAt (path ++ [u]) = (child u).nodeAt [] := by
  induction path generalizing k with
  | nil =>
      cases k with
      | zero => cases root; simp [nodeAt] at h
      | succ k =>
          cases root with
          | node rootOrder rootChild =>
              simp only [nodeAt] at h
              have hv := Option.some.inj h
              cases hv
              rfl
  | cons v path ih =>
      cases k with
      | zero => cases root; simp [nodeAt] at h
      | succ k =>
          cases root with
          | node rootOrder rootChild =>
              simp only [nodeAt, List.cons_append]
              exact ih (rootChild v) h

end RecursiveForkCoins

/-- Erasing a finite extractor tape produces complete executable coins. -/
theorem RecursiveForkTape.toCoins_complete {F : Type*} [Fintype F] [DecidableEq F] :
    {d : ℕ} → (tape : RecursiveForkTape F d) → tape.toCoins.Complete
  | 0, .leaf => trivial
  | _ + 1, .node order child => by
      constructor
      · exact RecursiveForkTape.mem_orderList order
      · intro u
        exact toCoins_complete (child u)

/-- A finite tape tries exactly one permutation of the challenge set at every node. -/
theorem RecursiveForkTape.toCoins_bounded {F : Type*} [Fintype F] [DecidableEq F] :
    {d : ℕ} → (tape : RecursiveForkTape F d) →
      tape.toCoins.Bounded (Fintype.card F)
  | 0, .leaf => trivial
  | _ + 1, .node order child => by
      constructor
      · simp [RecursiveForkTape.orderList]
      · intro u
        exact toCoins_bounded (child u)

/-- Three distinct nonzero challenges whose recursive attempts all succeed. -/
def ThreeForkSuccess {F : Type*} [Zero F] (good : F → Prop) : Prop :=
  ∃ u₁ u₂ u₃, u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
    u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧ good u₁ ∧ good u₂ ∧ good u₃

/-- The current challenge is exceptional when it is zero or recursively successful at a node that
does not have three distinct nonzero successful continuations. -/
noncomputable def recursiveForkEscape {F : Type*} [Zero F] (good : F → Prop) : Set F := by
  classical
  exact if ThreeForkSuccess good then {0} else {u | u = 0 ∨ good u}

/-- A recursive extractor escape set contains at most three challenges. -/
theorem recursiveForkEscape_subset_triple {F : Type*} [Zero F]
    (good : F → Prop) : ∃ a b : F, recursiveForkEscape good ⊆ {0, a, b} := by
  by_cases hthree : ThreeForkSuccess good
  · refine ⟨0, 0, ?_⟩
    rw [recursiveForkEscape, if_pos hthree]
    intro u hu
    simp only [Set.mem_singleton_iff] at hu
    simp [hu]
  · by_cases ha : ∃ a, a ≠ 0 ∧ good a
    · obtain ⟨a, ha0, hag⟩ := ha
      by_cases hb : ∃ b, b ≠ 0 ∧ b ≠ a ∧ good b
      · obtain ⟨b, hb0, hba, hbg⟩ := hb
        refine ⟨a, b, ?_⟩
        rw [recursiveForkEscape, if_neg hthree]
        intro c hc
        rcases hc with rfl | hcg
        · simp
        by_cases hc0 : c = 0
        · simp [hc0]
        by_cases hca : c = a
        · simp [hca]
        by_cases hcb : c = b
        · simp [hcb]
        exfalso
        apply hthree
        exact ⟨a, b, c, hba.symm, (fun h => hca h.symm), (fun h => hcb h.symm),
          ha0, hb0, hc0, hag, hbg, hcg⟩
      · refine ⟨a, a, ?_⟩
        rw [recursiveForkEscape, if_neg hthree]
        intro c hc
        rcases hc with rfl | hcg
        · simp
        by_cases hc0 : c = 0
        · simp [hc0]
        have hca : c = a := by
          by_contra hne
          exact hb ⟨c, hc0, hne, hcg⟩
        simp [hca]
    · refine ⟨0, 0, ?_⟩
      rw [recursiveForkEscape, if_neg hthree]
      intro c hc
      rcases hc with rfl | hcg
      · simp
      have hc0 : c = 0 := by
        by_contra hne
        exact ha ⟨c, hne, hcg⟩
      simp [hc0]

/-- The result of one extractor invocation and its exact adversary-run count. -/
structure RecursiveForkAttempt (α : Type*) where
  output : Option α
  runs : ℕ

namespace RecursiveForkAttempt

/-- Add already-spent adversary runs to an attempt. -/
def addRuns {α : Type*} (n : ℕ) (r : RecursiveForkAttempt α) : RecursiveForkAttempt α :=
  { output := r.output, runs := n + r.runs }

end RecursiveForkAttempt

/-- Scan until a fresh nonzero attempt succeeds, returning the remaining order and seen set. -/
def nextForkChallenge {F α : Type*} [Zero F] [DecidableEq F]
    (attempt : F → RecursiveForkAttempt α) (seen : List F) : List F →
    RecursiveForkAttempt ((F × α) × List F × List F)
  | [] => { output := none, runs := 0 }
  | u :: us =>
      if u = 0 ∨ u ∈ seen then
        nextForkChallenge attempt seen us
      else
        let current := attempt u
        match current.output with
        | some result =>
            { output := some ((u, result), (us, u :: seen))
              runs := current.runs }
        | none => (nextForkChallenge attempt seen us).addRuns current.runs

/-- Scanning reaches any eligible challenge whose recursive attempt succeeds. -/
theorem nextForkChallenge_isSome_of_good {F α : Type*} [Zero F] [DecidableEq F]
    (attempt : F → RecursiveForkAttempt α) (seen : List F) {u : F} {order : List F}
    (hmem : u ∈ order) (hu0 : u ≠ 0) (hseen : u ∉ seen)
    (hgood : (attempt u).output.isSome) :
    (nextForkChallenge attempt seen order).output.isSome := by
  induction order generalizing seen with
  | nil => simp at hmem
  | cons v order ih =>
      simp only [nextForkChallenge]
      split
      · apply ih seen
        rcases List.mem_cons.mp hmem with rfl | hmem
        · rename_i hskip
          exact absurd hskip (not_or_intro hu0 hseen)
        · exact hmem
        · exact hseen
      · cases hv : (attempt v).output with
        | some result => simp
        | none =>
            simp only [RecursiveForkAttempt.addRuns]
            apply ih seen
            · rcases List.mem_cons.mp hmem with rfl | hmem
              · simp [hv] at hgood
              · exact hmem
            · exact hseen

/-- Every other successful challenge lies in the suffix left after the first successful scan. -/
theorem nextForkChallenge_other_good_mem_rest {F α : Type*} [Zero F] [DecidableEq F]
    (attempt : F → RecursiveForkAttempt α) (seen : List F)
    {u : F} {order rest : List F} {selected : F} {result : α} {seen' : List F}
    (hout : (nextForkChallenge attempt seen order).output =
      some ((selected, result), (rest, seen')))
    (hmem : u ∈ order) (hu0 : u ≠ 0) (hseen : u ∉ seen)
    (hgood : (attempt u).output.isSome) (hne : u ≠ selected) : u ∈ rest := by
  induction order generalizing seen rest selected result seen' with
  | nil => simp at hmem
  | cons v order ih =>
      simp only [nextForkChallenge] at hout
      split at hout
      · apply ih seen hout
        · rcases List.mem_cons.mp hmem with rfl | hmem
          · rename_i hskip
            exact absurd hskip (not_or_intro hu0 hseen)
          · exact hmem
        · exact hseen
        · exact hne
      · cases hv : (attempt v).output with
        | none =>
            simp only [hv, RecursiveForkAttempt.addRuns] at hout
            apply ih seen hout
            · rcases List.mem_cons.mp hmem with rfl | hmem
              · simp [hv] at hgood
              · exact hmem
            · exact hseen
            · exact hne
        | some vResult =>
            simp only [hv, Option.some.injEq, Prod.mk.injEq] at hout
            obtain ⟨⟨hselected, _⟩, hrest, _⟩ := hout
            subst selected; subst rest
            rcases List.mem_cons.mp hmem with rfl | hmem
            · exact absurd rfl hne
            · exact hmem

/-- A successful scan returns a nonzero challenge outside the incoming seen set and adds exactly
that challenge to the set. -/
theorem nextForkChallenge_output_fresh {F α : Type*} [Zero F] [DecidableEq F]
    (attempt : F → RecursiveForkAttempt α) (seen : List F)
    {order rest : List F} {selected : F} {result : α} {seen' : List F}
    (hout : (nextForkChallenge attempt seen order).output =
      some ((selected, result), (rest, seen'))) :
    selected ≠ 0 ∧ selected ∉ seen ∧ seen' = selected :: seen := by
  induction order with
  | nil => simp [nextForkChallenge] at hout
  | cons u order ih =>
      simp only [nextForkChallenge] at hout
      split at hout
      · exact ih hout
      · rename_i hfresh
        cases hu : (attempt u).output with
        | none =>
            simp only [hu, RecursiveForkAttempt.addRuns] at hout
            exact ih hout
        | some uResult =>
            simp only [hu, Option.some.injEq, Prod.mk.injEq] at hout
            obtain ⟨⟨hselected, _⟩, _, hseen'⟩ := hout
            subst selected; subst seen'
            exact ⟨fun h => hfresh (Or.inl h), fun h => hfresh (Or.inr h), rfl⟩

/-- A successful scan returns the result of the selected recursive attempt. -/
theorem nextForkChallenge_output_attempt {F α : Type*} [Zero F] [DecidableEq F]
    (attempt : F → RecursiveForkAttempt α) (seen : List F)
    {order rest : List F} {selected : F} {result : α} {seen' : List F}
    (hout : (nextForkChallenge attempt seen order).output =
      some ((selected, result), (rest, seen'))) :
    (attempt selected).output = some result := by
  induction order with
  | nil => simp [nextForkChallenge] at hout
  | cons u order ih =>
      simp only [nextForkChallenge] at hout
      split at hout
      · exact ih hout
      · cases hu : (attempt u).output with
        | none =>
            simp only [hu, RecursiveForkAttempt.addRuns] at hout
            exact ih hout
        | some uResult =>
            simp only [hu, Option.some.injEq, Prod.mk.injEq] at hout
            obtain ⟨⟨hselected, hresult⟩, _, _⟩ := hout
            subst selected
            subst result
            exact hu

/-- The scanner charges at most one bounded attempt per challenge in its input order. -/
theorem nextForkChallenge_runs_le {F α : Type*} [Zero F] [DecidableEq F]
    (attempt : F → RecursiveForkAttempt α) (seen order : List F) (C : ℕ)
    (hC : ∀ u, (attempt u).runs ≤ C) :
    (nextForkChallenge attempt seen order).runs ≤ order.length * C := by
  induction order generalizing seen with
  | nil => simp [nextForkChallenge]
  | cons u order ih =>
      simp only [nextForkChallenge]
      split
      · simpa only [List.length_cons] using
          le_trans (ih seen) (Nat.mul_le_mul_right C (Nat.le_succ order.length))
      · cases hu : (attempt u).output with
        | some result =>
            simp only [List.length_cons]
            exact le_trans (hC u) (Nat.le_mul_of_pos_left C (Nat.succ_pos _))
        | none =>
            simp only [RecursiveForkAttempt.addRuns, List.length_cons]
            calc
              _ ≤ C + order.length * C := Nat.add_le_add (hC u) (ih seen)
              _ = (order.length + 1) * C := by ring

/-- A successful scan returns a suffix of its input order. -/
theorem nextForkChallenge_output_rest_length_le {F α : Type*} [Zero F] [DecidableEq F]
    (attempt : F → RecursiveForkAttempt α) (seen : List F)
    {order rest : List F} {selected : F} {result : α} {seen' : List F}
    (hout : (nextForkChallenge attempt seen order).output =
      some ((selected, result), (rest, seen'))) :
    rest.length ≤ order.length := by
  induction order with
  | nil => simp [nextForkChallenge] at hout
  | cons u order ih =>
      simp only [nextForkChallenge] at hout
      split at hout
      · exact (ih hout).trans (Nat.le_succ _)
      · cases hu : (attempt u).output with
        | none =>
            simp only [hu, RecursiveForkAttempt.addRuns] at hout
            exact (ih hout).trans (Nat.le_succ _)
        | some value =>
            simp only [hu, Option.some.injEq, Prod.mk.injEq] at hout
            obtain ⟨_, hrest, _⟩ := hout
            subst rest
            exact Nat.le_succ _

/-- If three distinct nonzero challenges succeed, two scans after any successful first challenge
find the two additional branches. -/
theorem nextForkChallenge_two_more {F α : Type*} [Zero F] [DecidableEq F]
    (attempt : F → RecursiveForkAttempt α) (order : List F)
    (hcomplete : ∀ u : F, u ∈ order) (first : F)
    (hthree : ThreeForkSuccess fun u => (attempt u).output.isSome) :
    ∃ u₂ c₂ rest seen,
      (nextForkChallenge attempt [first] order).output = some ((u₂, c₂), (rest, seen)) ∧
        (nextForkChallenge attempt seen rest).output.isSome := by
  obtain ⟨a, b, c, hab, hac, hbc, ha0, hb0, hc0, ha, hb, hc⟩ := hthree
  have pick : ∃ x y : F, x ≠ y ∧ x ≠ first ∧ y ≠ first ∧
      x ≠ 0 ∧ y ≠ 0 ∧ (attempt x).output.isSome ∧ (attempt y).output.isSome := by
    by_cases hfa : first = a
    · subst first
      exact ⟨b, c, hbc, hab.symm, hac.symm, hb0, hc0, hb, hc⟩
    by_cases hfb : first = b
    · subst first
      exact ⟨a, c, hac, hab, hbc.symm, ha0, hc0, ha, hc⟩
    · exact ⟨a, b, hab, fun h => hfa h.symm, fun h => hfb h.symm,
        ha0, hb0, ha, hb⟩
  obtain ⟨x, y, hxy, hxf, hyf, hx0, hy0, hx, hy⟩ := pick
  have hsecond := nextForkChallenge_isSome_of_good attempt [first]
    (hcomplete x) hx0 (by simp [hxf]) hx
  obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hsecond
  rcases out with ⟨⟨u₂, c₂⟩, rest, seen⟩
  have hfresh := nextForkChallenge_output_fresh attempt [first] hout
  let remaining := if x = u₂ then y else x
  have hrem_mem : remaining ∈ rest := by
    dsimp only [remaining]
    split
    · rename_i hxu
      apply nextForkChallenge_other_good_mem_rest attempt [first] hout
        (hcomplete y) hy0 (by simp [hyf]) hy
      intro hyu
      apply hxy
      exact hxu.trans hyu.symm
    · rename_i hxu
      exact nextForkChallenge_other_good_mem_rest attempt [first] hout
        (hcomplete x) hx0 (by simp [hxf]) hx hxu
  have hrem0 : remaining ≠ 0 := by
    dsimp only [remaining]; split <;> assumption
  have hremGood : (attempt remaining).output.isSome := by
    dsimp only [remaining]; split <;> assumption
  have hremNe : remaining ≠ u₂ := by
    dsimp only [remaining]
    split
    · rename_i hxu
      intro hyu
      exact hxy (hxu.trans hyu.symm)
    · assumption
  have hremSeen : remaining ∉ seen := by
    rw [hfresh.2.2]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨hremNe, ?_⟩
    dsimp only [remaining]
    split <;> assumption
  exact ⟨u₂, c₂, rest, seen, hout,
    nextForkChallenge_isSome_of_good attempt seen hrem_mem hrem0 hremSeen hremGood⟩

/-- Constructive decision procedure for the deployed certificate checker. -/
def decideDeployedForkValid {F G : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [DecidableEq G] [Module F G] :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) →
      (U W : G) → (z : F) → (Pwhole : G) → (cert : DForkCert F G d) →
      Decidable (DeployedForkValid g b U W z Pwhole cert)
  | 0, g, b, U, W, z, Pwhole, .leaf c f => by
      unfold DeployedForkValid
      infer_instance
  | d + 1, g, b, U, W, z, Pwhole, .node L R u₁ u₂ u₃ c₁ c₂ c₃ => by
      letI := decideDeployedForkValid (foldGens g u₁) (foldGens b u₁) U W z
        (Pwhole + u₁⁻¹ • L + u₁ • R) c₁
      letI := decideDeployedForkValid (foldGens g u₂) (foldGens b u₂) U W z
        (Pwhole + u₂⁻¹ • L + u₂ • R) c₂
      letI := decideDeployedForkValid (foldGens g u₃) (foldGens b u₃) U W z
        (Pwhole + u₃⁻¹ • L + u₃ • R) c₃
      change Decidable
        (u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
          DeployedForkValid (foldGens g u₁) (foldGens b u₁) U W z
              (Pwhole + u₁⁻¹ • L + u₁ • R) c₁ ∧
          DeployedForkValid (foldGens g u₂) (foldGens b u₂) U W z
              (Pwhole + u₂⁻¹ • L + u₂ • R) c₂ ∧
          DeployedForkValid (foldGens g u₃) (foldGens b u₃) U W z
              (Pwhole + u₃⁻¹ • L + u₃ • R) c₃)
      infer_instance

section Extractor

variable {T F G P ι : Type*} [DecidableEq T] [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [Fintype ι]

/-- Fork from a cached run, rejecting changed trunks until two further distinct nonzero challenges
succeed. -/
def recursiveAlgebraicForkFrom
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P)
    (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F)
    (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p)) :
    {d : ℕ} → (m : ℕ) → m + d = k → (O : T → F) → (p : P) →
      RecursiveForkCoins F d →
      RecursiveForkAttempt (AlgebraicDForkCert (F := F) basis d)
  | 0, _, _, O, p, .leaf => by
      letI := decideWin O p
      exact
        { output := if win O p then some (.leaf (final p).1 (final p).2) else none
          runs := 1 }
  | d + 1, m, hmk, O, p, .node order child => by
      have hm : m < k := by omega
      have htail : m + 1 + d = k := by omega
      let j : Fin k := ⟨m, hm⟩
      let t : T := prefixes (A.run O) j
      let u₁ : F := O t
      if hu₁ : u₁ = 0 then
        exact { output := none, runs := 1 }
      else
        let first := recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
          (m + 1) htail O p (child u₁)
        match hfirst : first.output with
        | none => exact { output := none, runs := first.runs }
        | some c₁ =>
          let candidate := fun u =>
            let O' := Function.update O t u
            let p' := A.run O'
            if prefixes p' j = t then
              recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                (m + 1) htail O' p' (child u)
            else
              { output := none, runs := 1 }
          let second := nextForkChallenge candidate [u₁] order
          match hsecond : second.output with
          | none => exact { output := none, runs := first.runs + second.runs }
          | some ((u₂, c₂), (rest, seen)) =>
            let third := nextForkChallenge candidate seen rest
            match hthird : third.output with
            | none =>
              exact { output := none, runs := first.runs + second.runs + third.runs }
            | some ((u₃, c₃), (_, _)) =>
              let L := (rounds p j).1
              let R := (rounds p j).2
              exact
                { output := some (.node R L u₁⁻¹ u₂⁻¹ u₃⁻¹ c₁ c₂ c₃)
                  runs := first.runs + second.runs + third.runs }
termination_by d => d

/-- Run the recursive extractor from an oracle table. -/
def recursiveAlgebraicFork
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P)
    (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F)
    (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p))
    (O : T → F) (coins : RecursiveForkCoins F k) :
    RecursiveForkAttempt (AlgebraicDForkCert (F := F) basis k) :=
  recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin 0 (by omega)
    O (A.run O) coins

/-! ## Worst-case run bound -/

/-- A bounded recursive tape makes at most `(2n+1)^d` adversary runs. -/
theorem recursiveAlgebraicForkFrom_runs_le
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P) (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p)) (n : ℕ) :
    {d : ℕ} → (m : ℕ) → (hmk : m + d = k) → (O : T → F) → (p : P) →
      (coins : RecursiveForkCoins F d) → coins.Bounded n →
      (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
        m hmk O p coins).runs ≤ (2 * n + 1) ^ d
  | 0, m, hmk, O, p, .leaf, _ => by
      simp [recursiveAlgebraicForkFrom]
  | d + 1, m, hmk, O, p, .node order child, hbounded => by
      have hm : m < k := by omega
      have htail : m + 1 + d = k := by omega
      let j : Fin k := ⟨m, hm⟩
      let t : T := prefixes (A.run O) j
      let u₁ : F := O t
      let C := (2 * n + 1) ^ d
      have hchild : ∀ u, (recursiveAlgebraicForkFrom basis k A prefixes rounds final
          win decideWin (m + 1) htail (Function.update O t u)
          (A.run (Function.update O t u)) (child u)).runs ≤ C := by
        intro u
        exact recursiveAlgebraicForkFrom_runs_le basis k A prefixes rounds final win decideWin n
          (m + 1) htail _ _ (child u) (hbounded.2 u)
      have hfirst : (recursiveAlgebraicForkFrom basis k A prefixes rounds final
          win decideWin (m + 1) htail O p (child u₁)).runs ≤ C :=
        recursiveAlgebraicForkFrom_runs_le basis k A prefixes rounds final win decideWin n
          (m + 1) htail O p (child u₁) (hbounded.2 u₁)
      let candidate := fun u =>
        let O' := Function.update O t u
        let p' := A.run O'
        if prefixes p' j = t then
          recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
            (m + 1) htail O' p' (child u)
        else { output := none, runs := 1 }
      have hcandidate : ∀ u, (candidate u).runs ≤ C := by
        intro u
        dsimp only [candidate]
        split
        · exact hchild u
        · simp only
          exact one_le_pow₀ (by omega)
      have hsecondRuns : (nextForkChallenge candidate [u₁] order).runs ≤ n * C := by
        refine (nextForkChallenge_runs_le candidate [u₁] order C hcandidate).trans ?_
        exact Nat.mul_le_mul_right C hbounded.1
      simp only [recursiveAlgebraicForkFrom]
      split
      · simp only
        have hC : 1 ≤ C := one_le_pow₀ (by omega)
        rw [Nat.pow_succ]
        exact hC.trans (Nat.le_mul_of_pos_right C (by omega))
      · split
        · rename_i hfirstNone
          simp only
          rw [Nat.pow_succ]
          exact hfirst.trans (Nat.le_mul_of_pos_right C (by omega))
        · rename_i c₁ hfirstSome
          split
          · rename_i hsecondNone
            simp only
            rw [Nat.pow_succ]
            calc
              _ ≤ C + n * C := Nat.add_le_add hfirst hsecondRuns
              _ ≤ C + 2 * (n * C) := by omega
              _ = C * (2 * n + 1) := by ring
          · rename_i u₂ c₂ rest seen hsecondSome
            have hrest := nextForkChallenge_output_rest_length_le candidate [u₁] hsecondSome
            have hthirdRuns : (nextForkChallenge candidate seen rest).runs ≤ n * C := by
              refine (nextForkChallenge_runs_le candidate seen rest C hcandidate).trans ?_
              exact Nat.mul_le_mul_right C (hrest.trans hbounded.1)
            split
            · simp only
              rw [Nat.pow_succ]
              calc
                _ ≤ C + n * C + n * C :=
                  Nat.add_le_add (Nat.add_le_add hfirst hsecondRuns) hthirdRuns
                _ = C * (2 * n + 1) := by ring
            · simp only
              rw [Nat.pow_succ]
              calc
                _ ≤ C + n * C + n * C :=
                  Nat.add_le_add (Nat.add_le_add hfirst hsecondRuns) hthirdRuns
                _ = C * (2 * n + 1) := by ring

/-- The complete deployed tape gives a deterministic run bound, hence the same bound on its
expectation under any distribution of oracle tables and tapes. -/
theorem recursiveAlgebraicFork_runs_le
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P) (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p)) [Fintype F]
    (O : T → F) (tape : RecursiveForkTape F k) :
    (recursiveAlgebraicFork basis k A prefixes rounds final win decideWin O tape.toCoins).runs
      ≤ (2 * Fintype.card F + 1) ^ k := by
  exact recursiveAlgebraicForkFrom_runs_le basis k A prefixes rounds final win decideWin
    (Fintype.card F) 0 (by omega) O (A.run O) tape.toCoins tape.toCoins_bounded

/-- The complete-tape expectation is at most `(2·|F|+1)^k`, not polynomial AFK. -/
theorem recursiveAlgebraicFork_sum_runs_le_unconditional
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P) (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p)) [Fintype F]
    (O : T → F) :
    ∑ tape : RecursiveForkTape F k,
        (recursiveAlgebraicFork basis k A prefixes rounds final win decideWin
          O tape.toCoins).runs
      ≤ (2 * Fintype.card F + 1) ^ k * Fintype.card (RecursiveForkTape F k) := by
  calc
    _ ≤ ∑ _tape : RecursiveForkTape F k, (2 * Fintype.card F + 1) ^ k :=
      Finset.sum_le_sum (fun tape _ =>
        recursiveAlgebraicFork_runs_le basis k A prefixes rounds final win decideWin O tape)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

/-- The unconditional run bound over uniform oracle-table and extractor-tape coins. -/
theorem recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional [Fintype T]
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P) (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p)) [Fintype F] :
    ∑ coins : (T → F) × RecursiveForkTape F k,
        (recursiveAlgebraicFork basis k A prefixes rounds final win decideWin
          coins.1 coins.2.toCoins).runs
      ≤ (2 * Fintype.card F + 1) ^ k *
        Fintype.card ((T → F) × RecursiveForkTape F k) := by
  calc
    _ ≤ ∑ _coins : (T → F) × RecursiveForkTape F k,
          (2 * Fintype.card F + 1) ^ k :=
      Finset.sum_le_sum (fun coins _ =>
        recursiveAlgebraicFork_runs_le basis k A prefixes rounds final win decideWin
          coins.1 coins.2)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

/-! ## Certificate semantics -/

/-- An explicit algebraic fork tree for `acc`, using the conventions of `DeployedForkValid`. -/
def AlgebraicForkRealizes (basis : ι → G) (decode : T → G × G) :
    {d : ℕ} → ((Fin d → T) → (Fin d → F) → F → F → Prop) →
      AlgebraicDForkCert (F := F) basis d → Prop
  | 0, acc, .leaf c f => acc Fin.elim0 Fin.elim0 c f
  | _ + 1, acc, .node L R v₁ v₂ v₃ c₁ c₂ c₃ =>
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
      v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₃ ≠ 0 ∧
      ∃ t : T, L.point = (decode t).2 ∧ R.point = (decode t).1 ∧
        AlgebraicForkRealizes basis decode
          (fun ts cs c f => acc (Fin.cons t ts) (Fin.cons v₁⁻¹ cs) c f) c₁ ∧
        AlgebraicForkRealizes basis decode
          (fun ts cs c f => acc (Fin.cons t ts) (Fin.cons v₂⁻¹ cs) c f) c₂ ∧
        AlgebraicForkRealizes basis decode
          (fun ts cs c f => acc (Fin.cons t ts) (Fin.cons v₃⁻¹ cs) c f) c₃

omit [DecidableEq T] [DecidableEq F] in
/-- Realization is monotone in its leaf relation. -/
theorem AlgebraicForkRealizes.mono (basis : ι → G) (decode : T → G × G) :
    {d : ℕ} → {acc acc' : (Fin d → T) → (Fin d → F) → F → F → Prop} →
    {cert : AlgebraicDForkCert (F := F) basis d} →
    (∀ ts cs c f, acc ts cs c f → acc' ts cs c f) →
    AlgebraicForkRealizes basis decode acc cert →
    AlgebraicForkRealizes basis decode acc' cert
  | 0, _, _, .leaf _ _, h, hreal => h _ _ _ _ hreal
  | d + 1, acc, acc', .node L R v₁ v₂ v₃ c₁ c₂ c₃, h, hreal => by
      rcases hreal with ⟨h₁₂, h₁₃, h₂₃, hv₁, hv₂, hv₃, t, hL, hR, hc₁, hc₂, hc₃⟩
      refine ⟨h₁₂, h₁₃, h₂₃, hv₁, hv₂, hv₃, t, hL, hR, ?_, ?_, ?_⟩
      · exact AlgebraicForkRealizes.mono basis decode
          (fun ts cs c f hleaf => h _ _ _ _ hleaf) hc₁
      · exact AlgebraicForkRealizes.mono basis decode
          (fun ts cs c f hleaf => h _ _ _ _ hleaf) hc₂
      · exact AlgebraicForkRealizes.mono basis decode
          (fun ts cs c f hleaf => h _ _ _ _ hleaf) hc₃

/-- A recursive run agrees with all fork points already fixed above the current node. -/
def RecursiveRunHistory (k m : ℕ) (hmk : m ≤ k) (prefixes : P → Fin k → T)
    (O : T → F) (p : P) (history : Fin m → T × F) : Prop :=
  ∀ i, prefixes p ⟨i.val, by omega⟩ = (history i).1 ∧ O (history i).1 = (history i).2

/-- Runs represented by one recursive invocation, retaining the fork points fixed above round
`m`. -/
def RecursiveRunSuffix (k m d : ℕ) (hmk : m + d = k)
    (A : OracleComp T F P) (prefixes : P → Fin k → T) (final : P → F × F)
    (win stable : (T → F) → P → Prop) (history : Fin m → T × F) :
    (Fin d → T) → (Fin d → F) → F → F → Prop :=
  fun ts cs c f => ∃ O p, p = A.run O ∧ win O p ∧
    stable O p ∧ RecursiveRunHistory k m (by omega) prefixes O p history ∧
    (∀ i : Fin d, prefixes p ⟨m + i.val, by omega⟩ = ts i) ∧
    (∀ i, O (ts i) = cs i) ∧ final p = (c, f)

/-- Every returned certificate records actual winning adversary runs. -/
theorem recursiveAlgebraicForkFrom_realizes
    (basis : ι → G) (k : ℕ) (A : OracleComp T F P)
    (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p)) (decode : T → G × G)
    (D : PrefixDecode T k prefixes) (stable : (T → F) → P → Prop)
    (stable_update : ∀ (m : ℕ) (hm : m < k) (O : T → F) (p : P) (u : F),
      stable O p →
      let t := prefixes p ⟨m, hm⟩
      let O' := Function.update O t u
      let p' := A.run O'
      prefixes p' ⟨m, hm⟩ = t → stable O' p')
    (hdecode : ∀ p j, ((rounds p j).1.point, (rounds p j).2.point) = decode (prefixes p j)) :
    {d : ℕ} → (m : ℕ) → (hmk : m + d = k) → (O : T → F) → (p : P) →
    (coins : RecursiveForkCoins F d) → (cert : AlgebraicDForkCert (F := F) basis d) →
    (history : Fin m → T × F) → p = A.run O →
    stable O p → RecursiveRunHistory k m (by omega) prefixes O p history →
    (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
      m hmk O p coins).output = some cert →
    AlgebraicForkRealizes basis decode
      (RecursiveRunSuffix k m d hmk A prefixes final win stable history) cert
  | 0, m, hmk, O, p, .leaf, cert, history, hp, hstable, hhistory, hout => by
      simp only [recursiveAlgebraicForkFrom] at hout
      split at hout
      · rename_i hwin
        simp only [Option.some.injEq] at hout
        subst cert
        refine ⟨O, p, hp, hwin, hstable, hhistory, ?_, ?_, rfl⟩
        · intro i; exact Fin.elim0 i
        · intro i; exact Fin.elim0 i
      · simp at hout
  | d + 1, m, hmk, O, p, .node order child, cert, history, hp, hstable, hhistory, hout => by
      have hm : m < k := by omega
      have htail : m + 1 + d = k := by omega
      let j : Fin k := ⟨m, hm⟩
      let t : T := prefixes (A.run O) j
      let u₁ : F := O t
      simp only [recursiveAlgebraicForkFrom] at hout
      split at hout
      · simp at hout
      · rename_i hu₁
        split at hout
        · simp at hout
        · rename_i c₁ hfirst
          let candidate := fun u =>
            let O' := Function.update O t u
            let p' := A.run O'
            if prefixes p' j = t then
              recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                (m + 1) htail O' p' (child u)
            else { output := none, runs := 1 }
          split at hout
          · simp at hout
          · rename_i u₂ c₂ rest seen hsecond
            have hsecondAttempt := nextForkChallenge_output_attempt candidate [u₁] hsecond
            have hfresh₂ := nextForkChallenge_output_fresh candidate [u₁] hsecond
            have hseen : seen = u₂ :: [u₁] := hfresh₂.2.2
            have hu₂₁ : u₂ ≠ u₁ := by simpa using hfresh₂.2.1
            split at hout
            · simp at hout
            · rename_i u₃ c₃ rest₃ seen₃ hthird
              simp only [Option.some.injEq] at hout
              subst cert
              have hthirdAttempt := nextForkChallenge_output_attempt candidate _ hthird
              have hfresh₃ := nextForkChallenge_output_fresh candidate _ hthird
              have hu₃₂ : u₃ ≠ u₂ := by
                rw [hseen] at hfresh₃
                have hpair : u₃ ≠ u₂ ∧ u₃ ≠ u₁ := by simpa using hfresh₃.2.1
                exact hpair.1
              have hu₃₁ : u₃ ≠ u₁ := by
                rw [hseen] at hfresh₃
                have hpair : u₃ ≠ u₂ ∧ u₃ ≠ u₁ := by simpa using hfresh₃.2.1
                exact hpair.2
              have hcandidate (u : F) (c : AlgebraicDForkCert (F := F) basis d)
                  (hc : (candidate u).output = some c) :
                  ∃ O' p', O' = Function.update O t u ∧ p' = A.run O' ∧
                    prefixes p' j = t ∧
                    (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                      (m + 1) htail O' p' (child u)).output = some c := by
                refine ⟨Function.update O t u, A.run (Function.update O t u), rfl, rfl, ?_⟩
                dsimp only [candidate] at hc
                split at hc
                · exact ⟨by assumption, hc⟩
                · simp at hc
              obtain ⟨O₂, p₂, hO₂, hp₂, ht₂, hc₂⟩ := hcandidate u₂ c₂ hsecondAttempt
              obtain ⟨O₃, p₃, hO₃, hp₃, ht₃, hc₃⟩ := hcandidate u₃ c₃ hthirdAttempt
              let nextHistory (u : F) : Fin (m + 1) → T × F := Fin.snoc history (t, u)
              have hhistoryFirst :
                  RecursiveRunHistory k (m + 1) (by omega) prefixes O p (nextHistory u₁) := by
                intro i
                refine Fin.lastCases ?_ (fun q => ?_) i
                · simp [nextHistory, t, j, hp, u₁]
                · simpa [nextHistory] using hhistory q
              have hhistoryUpdate (u : F) (O' : T → F) (p' : P)
                  (hO' : O' = Function.update O t u) (hp' : p' = A.run O')
                  (ht' : prefixes p' j = t) :
                  RecursiveRunHistory k (m + 1) (by omega) prefixes O' p' (nextHistory u) := by
                intro i
                refine Fin.lastCases ?_ (fun q => ?_) i
                · constructor
                  · simpa [nextHistory] using ht'
                  · subst O'
                    simp only [nextHistory, Fin.snoc_last]
                    simp [Function.update_apply]
                · have hq : (q.val : ℕ) < m := q.isLt
                  let qk : Fin k := ⟨q.val, by omega⟩
                  have hprefix : prefixes p' qk = prefixes p qk := by
                    calc
                      prefixes p' qk = D.chainAt (prefixes p' j) qk :=
                        (D.chainAt_prefixes p' j qk (by change q.val ≤ m; omega)).symm
                      _ = D.chainAt t qk := by rw [ht']
                      _ = D.chainAt (prefixes p j) qk := by simp [t, j, hp]
                      _ = prefixes p qk := D.chainAt_prefixes p j qk (by change q.val ≤ m; omega)
                  constructor
                  · simpa [nextHistory, qk] using hprefix.trans (hhistory q).1
                  · subst O'
                    rw [Function.update_apply]
                    split
                    · rename_i heq
                      have heq' : (history q).1 = t := by simpa [nextHistory] using heq
                      exfalso
                      have hne := D.chainAt_ne t qk
                      apply hne
                      · have hround : D.roundOf t = m := by
                          simpa [t, j] using D.roundOf_prefixes (A.run O) j
                        rw [hround]
                        omega
                      · rw [D.chainAt_prefixes (A.run O) j qk (by change q.val ≤ m; omega)]
                        simpa [t, hp, qk] using (hhistory q).1.trans heq'
                    · simpa [nextHistory] using (hhistory q).2
              have hstable₂ : stable O₂ p₂ := by
                subst O₂
                subst p₂
                have hs := stable_update m hm O p u₂ hstable
                have htp : prefixes p ⟨m, hm⟩ = t := by simp [t, j, hp]
                simpa [htp] using hs (by simpa [htp] using ht₂)
              have hstable₃ : stable O₃ p₃ := by
                subst O₃
                subst p₃
                have hs := stable_update m hm O p u₃ hstable
                have htp : prefixes p ⟨m, hm⟩ = t := by simp [t, j, hp]
                simpa [htp] using hs (by simpa [htp] using ht₃)
              have hr₁ := recursiveAlgebraicForkFrom_realizes basis k A prefixes rounds final
                win decideWin decode D stable stable_update hdecode
                  (m + 1) htail O p (child u₁) c₁
                  (nextHistory u₁) hp hstable hhistoryFirst hfirst
              have hr₂ := recursiveAlgebraicForkFrom_realizes basis k A prefixes rounds final
                win decideWin decode D stable stable_update hdecode
                  (m + 1) htail O₂ p₂ (child u₂) c₂
                  (nextHistory u₂) hp₂ hstable₂
                  (hhistoryUpdate u₂ O₂ p₂ hO₂ hp₂ ht₂) hc₂
              have hr₃ := recursiveAlgebraicForkFrom_realizes basis k A prefixes rounds final
                win decideWin decode D stable stable_update hdecode
                  (m + 1) htail O₃ p₃ (child u₃) c₃
                  (nextHistory u₃) hp₃ hstable₃
                  (hhistoryUpdate u₃ O₃ p₃ hO₃ hp₃ ht₃) hc₃
              have hpoint : ((rounds p j).1.point, (rounds p j).2.point) = decode t := by
                simpa [t, hp] using hdecode p j
              refine ⟨fun h => hu₂₁ (inv_injective h).symm,
                fun h => hu₃₁ (inv_injective h).symm,
                fun h => hu₃₂ (inv_injective h).symm,
                inv_ne_zero hu₁, inv_ne_zero hfresh₂.1, inv_ne_zero hfresh₃.1,
                t, congrArg Prod.snd hpoint, congrArg Prod.fst hpoint, ?_, ?_, ?_⟩
              · apply AlgebraicForkRealizes.mono basis decode _ hr₁
                rintro ts cs c f ⟨O', p', hp', hwin', hstable', hhist', hts, hcs, hfinal⟩
                have hlast := hhist' (Fin.last m)
                have hhist : RecursiveRunHistory k m (by omega) prefixes O' p' history := by
                  intro q
                  simpa [nextHistory] using hhist' q.castSucc
                refine ⟨O', p', hp', hwin', hstable', hhist, ?_, ?_, hfinal⟩
                · intro i
                  refine Fin.cases ?_ (fun q => ?_) i
                  · simpa [nextHistory] using hlast.1
                  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hts q
                · intro i
                  refine Fin.cases ?_ (fun q => ?_) i
                  · simpa [nextHistory] using hlast.2
                  · simpa using hcs q
              · apply AlgebraicForkRealizes.mono basis decode _ hr₂
                rintro ts cs c f ⟨O', p', hp', hwin', hstable', hhist', hts, hcs, hfinal⟩
                have hlast := hhist' (Fin.last m)
                have hhist : RecursiveRunHistory k m (by omega) prefixes O' p' history := by
                  intro q
                  simpa [nextHistory] using hhist' q.castSucc
                refine ⟨O', p', hp', hwin', hstable', hhist, ?_, ?_, hfinal⟩
                · intro i
                  refine Fin.cases ?_ (fun q => ?_) i
                  · simpa [nextHistory] using hlast.1
                  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hts q
                · intro i
                  refine Fin.cases ?_ (fun q => ?_) i
                  · simpa [nextHistory] using hlast.2
                  · simpa using hcs q
              · apply AlgebraicForkRealizes.mono basis decode _ hr₃
                rintro ts cs c f ⟨O', p', hp', hwin', hstable', hhist', hts, hcs, hfinal⟩
                have hlast := hhist' (Fin.last m)
                have hhist : RecursiveRunHistory k m (by omega) prefixes O' p' history := by
                  intro q
                  simpa [nextHistory] using hhist' q.castSucc
                refine ⟨O', p', hp', hwin', hstable', hhist, ?_, ?_, hfinal⟩
                · intro i
                  refine Fin.cases ?_ (fun q => ?_) i
                  · simpa [nextHistory] using hlast.1
                  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hts q
                · intro i
                  refine Fin.cases ?_ (fun q => ?_) i
                  · simpa [nextHistory] using hlast.2
                  · simpa using hcs q

end Extractor

section FpValidity

variable {T G ι : Type*} [AddCommGroup G] [Module Fp G] [Fintype ι]

/-- A realized algebraic tree whose leaves satisfy the deployed flat verifier equation erases to
a valid deployed fork certificate. -/
theorem AlgebraicForkRealizes.deployedForkValid (basis : ι → G)
    (decode : T → G × G) (U W : G) (z : Fp) :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → Fp) → (Pwhole : G) →
    (acc : (Fin d → T) → (Fin d → Fp) → Fp → Fp → Prop) →
    (cert : AlgebraicDForkCert (F := Fp) basis d) →
    AlgebraicForkRealizes basis decode acc cert →
    (∀ ts cs c f, acc ts cs c f →
      flatAccept (proverOfRounds (fun j => decode (ts j)) c f)
        g b U W z Pwhole cs) →
    DeployedForkValid g b U W z Pwhole cert.toDForkCert
  | 0, g, b, Pwhole, acc, .leaf c f, hreal, hacc => hacc _ _ _ _ hreal
  | d + 1, g, b, Pwhole, acc, .node L R v₁ v₂ v₃ c₁ c₂ c₃, hreal, hacc => by
      rcases hreal with ⟨h₁₂, h₁₃, h₂₃, hv₁, hv₂, hv₃, t, hL, hR, hc₁, hc₂, hc₃⟩
      refine ⟨h₁₂, h₁₃, h₂₃, hv₁, hv₂, hv₃, ?_, ?_, ?_⟩
      · apply AlgebraicForkRealizes.deployedForkValid basis decode U W z
          (acc := fun ts cs c f => acc (Fin.cons t ts) (Fin.cons v₁⁻¹ cs) c f)
        · exact hc₁
        · intro ts cs c f hleaf
          have hfull := hacc (Fin.cons t ts) (Fin.cons v₁⁻¹ cs) c f hleaf
          rw [proverOfRounds, flatAccept] at hfull
          simpa only [Fin.cons_zero, Fin.tail_cons, inv_inv, hL, hR,
            add_assoc, add_left_comm, add_comm] using hfull
      · apply AlgebraicForkRealizes.deployedForkValid basis decode U W z
          (acc := fun ts cs c f => acc (Fin.cons t ts) (Fin.cons v₂⁻¹ cs) c f)
        · exact hc₂
        · intro ts cs c f hleaf
          have hfull := hacc (Fin.cons t ts) (Fin.cons v₂⁻¹ cs) c f hleaf
          rw [proverOfRounds, flatAccept] at hfull
          simpa only [Fin.cons_zero, Fin.tail_cons, inv_inv, hL, hR,
            add_assoc, add_left_comm, add_comm] using hfull
      · apply AlgebraicForkRealizes.deployedForkValid basis decode U W z
          (acc := fun ts cs c f => acc (Fin.cons t ts) (Fin.cons v₃⁻¹ cs) c f)
        · exact hc₃
        · intro ts cs c f hleaf
          have hfull := hacc (Fin.cons t ts) (Fin.cons v₃⁻¹ cs) c f hleaf
          rw [proverOfRounds, flatAccept] at hfull
          simpa only [Fin.cons_zero, Fin.tail_cons, inv_inv, hL, hR,
            add_assoc, add_left_comm, add_comm] using hfull

end FpValidity

section Extractor

variable {T F G P ι : Type*} [DecidableEq T] [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [Fintype ι]

/-! ## Operational escape event -/

/-- The root tape reaches the coins used at round `m` along the current run's earlier challenges. -/
def RecursiveForkReached (k : ℕ) (prefixes : P → Fin k → T)
    (root : RecursiveForkCoins F k) :
    {d : ℕ} → (m : ℕ) → m + d = k → (O : T → F) → (p : P) →
      RecursiveForkCoins F d → Prop
  | 0, _, _, _, _, .leaf => True
  | d + 1, m, _, O, p, .node order child =>
      root.nodeAt ((List.ofFn fun i : Fin k => O (prefixes p i)).take m) =
          some ⟨d, order, child⟩

omit [DecidableEq T] [Field F] [DecidableEq F] in
/-- Extending a reached node by its current challenge reaches the selected child coins. -/
theorem recursiveForkReached_child (k : ℕ) (prefixes : P → Fin k → T)
    (root : RecursiveForkCoins F k) {d m : ℕ} (hmk : m + (d + 1) = k)
    (O : T → F) (p : P) (order : List F) (child : F → RecursiveForkCoins F d)
    (hreach : RecursiveForkReached k prefixes root m hmk O p (.node order child)) :
    RecursiveForkReached k prefixes root (m + 1) (by omega) O p
      (child (O (prefixes p ⟨m, by omega⟩))) := by
  cases d with
  | zero =>
      cases hc : child (O (prefixes p ⟨m, by omega⟩))
      simp [RecursiveForkReached]
  | succ d =>
      unfold RecursiveForkReached at hreach
      let all : List F := List.ofFn fun i : Fin k => O (prefixes p i)
      let path : List F := all.take m
      let u := O (prefixes p ⟨m, by omega⟩)
      have hnext : all.take (m + 1) = path ++ [u] := by
        rw [List.take_add_one]
        have hm : m < all.length := by simp [all]; omega
        rw [List.getElem?_eq_getElem hm]
        simp only [Option.toList_some, path, all, List.getElem_ofFn]
        congr
      have hn := RecursiveForkCoins.nodeAt_append_singleton root path u order child hreach
      cases hc : child u with
      | node childOrder grandchild =>
          unfold RecursiveForkReached
          change root.nodeAt (all.take (m + 1)) = _
          rw [hnext]
          simpa only [hc, RecursiveForkCoins.nodeAt] using hn

/-- Escape sets for one tape: zero and successful replacements at nodes with fewer than three
distinct nonzero successes. -/
noncomputable def recursiveForkEscapeSet
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P) (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p))
    (D : PrefixDecode T k prefixes) (root : RecursiveForkCoins F k) :
    T → (T → F) → Set F := by
  intro t O
  if hm : D.roundOf t < k then
    let j : Fin k := ⟨D.roundOf t, hm⟩
    let path : List F :=
      (List.ofFn fun i : Fin k => O (D.chainAt t i)).take (D.roundOf t)
    match root.nodeAt path with
    | none => exact ∅
    | some node =>
      if hd : D.roundOf t + 1 + node.depth = k then
        exact recursiveForkEscape fun u =>
          let O' := Function.update O t u
          let p' := A.run O'
          prefixes p' j = t ∧
            (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
              (D.roundOf t + 1) hd O' p' (node.child u)).output.isSome
      else exact ∅
  else exact ∅

/-- The operational escape set is blind at the point whose answer it prices. -/
theorem recursiveForkEscapeSet_blind
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P) (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p))
    (D : PrefixDecode T k prefixes) (root : RecursiveForkCoins F k)
    (t : T) (O : T → F) (v : F) :
    recursiveForkEscapeSet basis k A prefixes rounds final win decideWin D root t
        (Function.update O t v) =
      recursiveForkEscapeSet basis k A prefixes rounds final win decideWin D root t O := by
  rw [recursiveForkEscapeSet, recursiveForkEscapeSet]
  by_cases hm : D.roundOf t < k
  · simp only [dif_pos hm]
    let path : List F :=
      (List.ofFn fun i : Fin k => O (D.chainAt t i)).take (D.roundOf t)
    have hpath :
        (List.ofFn (fun i : Fin k => Function.update O t v (D.chainAt t i))).take
            (D.roundOf t) = path := by
      apply List.ext_getElem
      · simp [path]
      · intro i hi hi'
        rw [List.getElem_take, List.getElem_take, List.getElem_ofFn, List.getElem_ofFn,
          Function.update_apply, if_neg]
        apply D.chainAt_ne t
        have hlen : path.length = D.roundOf t := by simp [path, Nat.min_eq_left (Nat.le_of_lt hm)]
        rw [hlen] at hi'
        exact hi'
    rw [hpath]
    generalize hnode : root.nodeAt path = node?
    cases node? with
    | none => simp
    | some node =>
        simp only
        by_cases hd : D.roundOf t + 1 + node.depth = k
        · simp only [dif_pos hd]
          congr 1
          funext u
          simp only [Function.update_idem]
        · simp [hd]
  · simp [hm]

/-- Each operational escape set has uniform measure at most `3 / |F|`. -/
theorem recursiveForkEscapeSet_measure_le [Fintype F]
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P) (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p))
    (D : PrefixDecode T k prefixes) (root : RecursiveForkCoins F k)
    (t : T) (O : T → F) :
    (PMF.uniformOfFintype F).toOuterMeasure
        (recursiveForkEscapeSet basis k A prefixes rounds final win decideWin D root t O)
      ≤ 3 / Fintype.card F := by
  rw [recursiveForkEscapeSet]
  by_cases hm : D.roundOf t < k
  · simp only [dif_pos hm]
    let path : List F :=
      (List.ofFn fun i : Fin k => O (D.chainAt t i)).take (D.roundOf t)
    generalize hnode : root.nodeAt path = node?
    cases node? with
    | none => simp
    | some node =>
        simp only
        by_cases hd : D.roundOf t + 1 + node.depth = k
        · simp only [dif_pos hd]
          obtain ⟨a, b, hab⟩ := recursiveForkEscape_subset_triple (fun u =>
            let O' := Function.update O t u
            let p' := A.run O'
            prefixes p' ⟨D.roundOf t, hm⟩ = t ∧
              (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
                (D.roundOf t + 1) hd O' p' (node.child u)).output.isSome)
          exact uniformOfFintype_toOuterMeasure_triple_le hab
        · simp [hd]
  · simp [hm]

/-- At a real round prefix, the global escape function is exactly the local node's exceptional
challenge set. -/
theorem recursiveForkEscapeSet_prefix
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P) (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p))
    (D : PrefixDecode T k prefixes) (root : RecursiveForkCoins F k)
    {d m : ℕ} (hmk : m + (d + 1) = k) (O : T → F) (p : P)
    (order : List F) (child : F → RecursiveForkCoins F d)
    (hreach : RecursiveForkReached k prefixes root m hmk O p (.node order child)) :
    recursiveForkEscapeSet basis k A prefixes rounds final win decideWin D root
        (prefixes p ⟨m, by omega⟩) O =
      recursiveForkEscape fun u =>
        let t := prefixes p ⟨m, by omega⟩
        let O' := Function.update O t u
        let p' := A.run O'
        prefixes p' ⟨m, by omega⟩ = t ∧
          (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
            (m + 1) (by omega) O' p' (child u)).output.isSome := by
  rw [recursiveForkEscapeSet]
  have hm : D.roundOf (prefixes p ⟨m, by omega⟩) < k := by
    rw [D.roundOf_prefixes]
    omega
  simp only [dif_pos hm]
  simp only [D.roundOf_prefixes]
  have hpath :
      (List.ofFn (fun i : Fin k => O (D.chainAt (prefixes p ⟨m, by omega⟩) i))).take m =
        (List.ofFn fun i : Fin k => O (prefixes p i)).take m := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      rw [List.getElem_take, List.getElem_take, List.getElem_ofFn, List.getElem_ofFn,
        D.chainAt_prefixes]
      have hlen : ((List.ofFn fun i : Fin k => O (prefixes p i)).take m).length = m := by
        simp
        omega
      rw [hlen] at hi'
      exact Nat.le_of_lt hi'
  rw [hpath]
  rw [hreach]
  simp only [dif_pos (show m + 1 + d = k by omega)]

/-- An accepting run that avoids the operational escape event is converted by the recursive
extractor into an explicit algebraic fork certificate. -/
theorem recursiveAlgebraicForkFrom_isSome_of_not_escape [Fintype F]
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P) (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p))
    (D : PrefixDecode T k prefixes) (root : RecursiveForkCoins F k) :
    {d : ℕ} → (m : ℕ) → (hmk : m + d = k) → (O : T → F) → (p : P) →
      (coins : RecursiveForkCoins F d) →
      p = A.run O → RecursiveForkReached k prefixes root m hmk O p coins →
      coins.Complete → win O p →
      ¬ (A.completing prefixes).escapesDuringC
        (recursiveForkEscapeSet basis k A prefixes rounds final win decideWin D root) O →
      (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
        m hmk O p coins).output.isSome
  | 0, m, hmk, O, p, .leaf, _, _, _, hwin, _ => by
      simp only [recursiveAlgebraicForkFrom]
      simp [hwin]
  | d + 1, m, hmk, O, p, .node order child, hp, hreach, hcomplete, hwin, hnoescape => by
      subst p
      have hm : m < k := by omega
      have htail : m + 1 + d = k := by omega
      let j : Fin k := ⟨m, hm⟩
      let t : T := prefixes (A.run O) j
      let u₁ : F := O t
      let esc := recursiveForkEscapeSet basis k A prefixes rounds final win decideWin D root
      let good : F → Prop := fun u =>
        let O' := Function.update O t u
        let p' := A.run O'
        prefixes p' j = t ∧
          (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
            (m + 1) htail O' p' (child u)).output.isSome
      have hesc : esc t O = recursiveForkEscape good := by
        simpa only [esc, good, t, j] using
          recursiveForkEscapeSet_prefix basis k A prefixes rounds final win decideWin D root
            hmk O (A.run O) order child hreach
      have hlocal : u₁ ∉ recursiveForkEscape good := by
        intro hu
        apply hnoescape
        apply OracleComp.escapesDuringC_completing esc prefixes (j := j)
        rw [show prefixes (A.run O) j = t from rfl, hesc]
        exact hu
      have hu₁ : u₁ ≠ 0 := by
        intro hu
        apply hlocal
        rw [recursiveForkEscape]
        split <;> simp [hu]
      have hreachChild : RecursiveForkReached k prefixes root (m + 1) htail O (A.run O) (child u₁) :=
        by simpa only [u₁, t, j] using
          recursiveForkReached_child k prefixes root hmk O (A.run O) order child hreach
      have hfirst :
          (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
            (m + 1) htail O (A.run O) (child u₁)).output.isSome :=
        recursiveAlgebraicForkFrom_isSome_of_not_escape basis k A prefixes rounds final win
          decideWin D root (m + 1) htail O (A.run O) (child u₁) rfl hreachChild
          (hcomplete.2 u₁) hwin hnoescape
      have hgood₁ : good u₁ := by
        dsimp only [good]
        rw [show Function.update O t u₁ = O from by
          funext q
          by_cases hq : q = t
          · subst q; simp [u₁]
          · simp [hq]]
        exact ⟨rfl, hfirst⟩
      have hthree : ThreeForkSuccess good := by
        by_contra hthree
        apply hlocal
        rw [recursiveForkEscape, if_neg hthree]
        exact Or.inr hgood₁
      let candidate := fun u =>
        let O' := Function.update O t u
        let p' := A.run O'
        if prefixes p' j = t then
          recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
            (m + 1) htail O' p' (child u)
        else { output := none, runs := 1 }
      have hcandidate : ∀ u, good u ↔ (candidate u).output.isSome := by
        intro u
        dsimp only [good, candidate]
        split
        · simp_all
        · simp_all
      have hthreeCandidate : ThreeForkSuccess fun u => (candidate u).output.isSome := by
        obtain ⟨a, b, c, hab, hac, hbc, ha0, hb0, hc0, ha, hb, hc⟩ := hthree
        exact ⟨a, b, c, hab, hac, hbc, ha0, hb0, hc0,
          (hcandidate a).mp ha, (hcandidate b).mp hb, (hcandidate c).mp hc⟩
      obtain ⟨u₂, c₂, rest, seen, hsecond, hthird⟩ :=
        nextForkChallenge_two_more candidate order hcomplete.1 u₁ hthreeCandidate
      obtain ⟨thirdOut, hthirdOut⟩ := Option.isSome_iff_exists.mp hthird
      rcases thirdOut with ⟨⟨u₃, c₃⟩, rest₃, seen₃⟩
      obtain ⟨c₁, hc₁⟩ := Option.isSome_iff_exists.mp hfirst
      dsimp only [u₁, t, j, candidate] at hu₁ hc₁ hsecond hthirdOut ⊢
      simp only [recursiveAlgebraicForkFrom]
      split
      · contradiction
      · split
        · simp_all
        · split
          · simp_all
          · split
            · simp_all
            · simp

/-- Root form: an accepting FS run that avoids the tape's escape event produces a certificate. -/
theorem recursiveAlgebraicFork_isSome_of_not_escape [Fintype F]
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P) (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p))
    (D : PrefixDecode T k prefixes) (coins : RecursiveForkCoins F k)
    (hcomplete : coins.Complete) (O : T → F) (hwin : win O (A.run O))
    (hnoescape : ¬ (A.completing prefixes).escapesDuringC
      (recursiveForkEscapeSet basis k A prefixes rounds final win decideWin D coins) O) :
    (recursiveAlgebraicFork basis k A prefixes rounds final win decideWin O coins).output.isSome := by
  apply recursiveAlgebraicForkFrom_isSome_of_not_escape basis k A prefixes rounds final win
    decideWin D coins 0 (by omega) O (A.run O) coins
  · rfl
  · cases k with
    | zero => cases coins; trivial
    | succ k => cases coins with
      | node order child => rfl
  · exact hcomplete
  · exact hwin
  · exact hnoescape

/-- Accepted oracle tables on which the executable recursive extractor fails. -/
noncomputable def recursiveForkFailureSet [Fintype T] [Fintype F]
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P) (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p)) (coins : RecursiveForkCoins F k) :
    Set (T → F) :=
  {O | win O (A.run O) ∧
    ¬ (recursiveAlgebraicFork basis k A prefixes rounds final win decideWin O coins).output.isSome}

/-- The complete recursive extractor fails on at most the operational query-loss slice. -/
theorem recursiveForkFailure_measure_le [Fintype T] [Fintype F] [Nonempty F]
    (basis : ι → G) (k : ℕ)
    (A : OracleComp T F P) (prefixes : P → Fin k → T)
    (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
    (final : P → F × F) (win : (T → F) → P → Prop)
    (decideWin : ∀ O p, Decidable (win O p))
    (D : PrefixDecode T k prefixes) (coins : RecursiveForkCoins F k)
    (hcomplete : coins.Complete) {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
        (recursiveForkFailureSet basis k A prefixes rounds final win decideWin coins)
      ≤ (Q + k) * (3 / Fintype.card F) := by
  let esc := recursiveForkEscapeSet basis k A prefixes rounds final win decideWin D coins
  have hsub : recursiveForkFailureSet basis k A prefixes rounds final win decideWin coins ⊆
      {O : T → F | (A.completing prefixes).escapesDuringC esc O} := by
    intro O hO
    rcases hO with ⟨hwin, hfail⟩
    by_contra hno
    exact hfail (recursiveAlgebraicFork_isSome_of_not_escape basis k A prefixes rounds final win
      decideWin D coins hcomplete O hwin hno)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  simpa only [Nat.cast_add] using
    (escapesDuringC_measure_le' esc
      (recursiveForkEscapeSet_blind basis k A prefixes rounds final win decideWin D coins)
      (recursiveForkEscapeSet_measure_le basis k A prefixes rounds final win decideWin D coins)
      (OracleComp.queryBound_completing prefixes hQ))

end Extractor

end Zcash.Snark
