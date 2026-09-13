import Zcash.Snark.ZeroKnowledge.LookupSort

/-!
# Valid lookup inputs make the specified sorter succeed

Canonical sorting makes run starts distinct. Each reserved value therefore consumes
only one available table occurrence, even when the input repeats that value many
times. Equal prefix lengths leave exactly enough unused values for the unreserved
slots. No multiset-containment premise is imposed on the input: ordinary membership
in the table suffices.
-/

namespace Zcash.Snark.ZeroKnowledge

variable {A : Type*}

/-- Distinct reserved values all present in the table can be consumed successfully. -/
theorem reserveLookupValues_exists [DecidableEq A] (reserved table : List A)
    (hnodup : reserved.Nodup) (hsubset : reserved ⊆ table) :
    ∃ unused, reserveLookupValues reserved table = some unused := by
  induction reserved generalizing table with
  | nil => exact ⟨table, rfl⟩
  | cons a rest ih =>
    obtain ⟨haRest, hrest⟩ := List.nodup_cons.mp hnodup
    have ha : a ∈ table := hsubset (List.mem_cons_self ..)
    have hsubRest : rest ⊆ table.erase a := by
      intro x hx
      apply (List.mem_erase_of_ne (show x ≠ a from fun h => haRest (h ▸ hx))).mpr
      exact hsubset (List.mem_cons_of_mem _ hx)
    obtain ⟨unused, h⟩ := ih (table.erase a) hrest hsubRest
    exact ⟨unused, by rw [reserveLookupValues, if_pos ha]; exact h⟩

/-- Reserved values occupy at most the number of plan slots. -/
theorem lookupPlan_reserved_le_length (plan : List (Option A)) :
    (plan.filterMap id).length ≤ plan.length := by
  induction plan with
  | nil => simp
  | cons entry rest ih =>
    cases entry with
    | none => exact le_trans ih (Nat.le_succ _)
    | some _ => exact Nat.succ_le_succ ih

/-- The exact remaining-slot count makes filling succeed. -/
theorem fillLookupPlan_exists (plan : List (Option A)) (unused : List A)
    (hlen : unused.length + (plan.filterMap id).length = plan.length) :
    ∃ output, fillLookupPlan plan unused = some output := by
  induction plan generalizing unused with
  | nil =>
    cases unused with
    | nil => exact ⟨[], rfl⟩
    | cons a rest => simp at hlen
  | cons entry rest ih =>
    cases entry with
    | some a =>
      change unused.length + ((rest.filterMap id).length + 1) = rest.length + 1 at hlen
      obtain ⟨output, houtput⟩ := ih unused (by omega)
      exact ⟨a :: output, by rw [fillLookupPlan, houtput]; rfl⟩
    | none =>
      have hbound := lookupPlan_reserved_le_length rest
      cases unused with
      | nil =>
        change 0 + (rest.filterMap id).length = rest.length + 1 at hlen
        omega
      | cons a unused =>
        change unused.length + 1 + (rest.filterMap id).length = rest.length + 1 at hlen
        obtain ⟨output, houtput⟩ := ih unused (by omega)
        exact ⟨a :: output, by rw [fillLookupPlan, houtput]; rfl⟩

/-- Sorted input reserves each distinct value once, in strictly increasing key order. -/
theorem lookupRunPlan_reservations [DecidableEq A] (key : A → ℕ) (hkey : Function.Injective key)
    (previous : Option A) (input : List A)
    (hsorted : input.Pairwise (fun a b => key a ≤ key b))
    (hprevious : ∀ p, previous = some p → ∀ a ∈ input, key p ≤ key a) :
    ((lookupRunPlan previous input).filterMap id).Nodup ∧
      (lookupRunPlan previous input).filterMap id ⊆ input ∧
      ∀ p, previous = some p → ∀ a ∈ (lookupRunPlan previous input).filterMap id, key p < key a := by
  induction input generalizing previous with
  | nil => simp [lookupRunPlan]
  | cons a rest ih =>
    obtain ⟨ha, hrest⟩ := List.pairwise_cons.mp hsorted
    have hprevRest : ∀ p, some a = some p → ∀ x ∈ rest, key p ≤ key x := by
      intro p hp x hx
      have hp' := Option.some.inj hp
      subst p
      exact ha x hx
    obtain ⟨hnodup, hsubset, hgreater⟩ := ih (some a) hrest hprevRest
    by_cases hrepeat : previous = some a
    · subst previous
      simp only [lookupRunPlan, List.filterMap_cons, id_eq]
      exact ⟨hnodup, fun _ hx => List.mem_cons_of_mem _ (hsubset hx), hgreater⟩
    · simp only [lookupRunPlan, if_neg hrepeat, List.filterMap_cons, id_eq]
      refine ⟨List.nodup_cons.mpr ⟨?_, hnodup⟩, ?_, ?_⟩
      · intro h
        exact Nat.lt_irrefl (key a) (hgreater a rfl a h)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hsubset hx)
      · intro p hp x hx
        have hle : key p ≤ key a := hprevious p hp a (List.mem_cons_self ..)
        have hne : key p ≠ key a := fun h => hrepeat (hp.trans (congrArg some (hkey h)))
        have hlt : key p < key a := by omega
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hlt
        · exact lt_trans hlt (hgreater a rfl x hx)

/-- Equal-length valid lookup prefixes make the sorter succeed. That the columns it returns
are permutations is `lookupSortColumns_correct`, not this statement. -/
theorem lookupSortColumns_exists [DecidableEq A] (key : A → ℕ) (hkey : Function.Injective key)
    (input table : List A) (hlen : input.length = table.length) (hsubset : input ⊆ table) :
    ∃ output, lookupSortColumns key input table = some output := by
  let b := canonicalLookupSort key input
  let sortedTable := canonicalLookupSort key table
  let plan := lookupRunPlan none b
  obtain ⟨hnodup, hreserved, _⟩ := lookupRunPlan_reservations key hkey none b
    (canonicalLookupSort_ordered key input) (fun p hp => by cases hp)
  have hsub : plan.filterMap id ⊆ sortedTable := by
    intro x hx
    exact (canonicalLookupSort_perm key table).mem_iff.mpr
      (hsubset ((canonicalLookupSort_perm key input).mem_iff.mp (hreserved hx)))
  obtain ⟨unused, hreserve⟩ := reserveLookupValues_exists (plan.filterMap id) sortedTable hnodup hsub
  have hsplit := (reserveLookupValues_perm _ _ _ hreserve).length_eq
  have hb := (canonicalLookupSort_perm key input).length_eq
  have ht := (canonicalLookupSort_perm key table).length_eq
  have hp := lookupRunPlan_length (none : Option A) b
  have hfillLen : unused.reverse.length + (plan.filterMap id).length = plan.length := by
    rw [List.length_reverse]
    rw [List.length_append] at hsplit
    change b.length = input.length at hb
    change sortedTable.length = table.length at ht
    change plan.length = b.length at hp
    omega
  obtain ⟨t, hfill⟩ := fillLookupPlan_exists plan unused.reverse hfillLen
  refine ⟨(b, t), ?_⟩
  simp only [lookupSortColumns, hlen, ne_eq, not_true_eq_false, if_false]
  change (reserveLookupValues (plan.filterMap id) sortedTable).bind
    (fun spare => (fillLookupPlan plan spare.reverse).bind (fun values => some (b, values))) = some (b, t)
  rw [hreserve]
  simp only [Option.bind_some]
  rw [hfill]
  rfl

end Zcash.Snark.ZeroKnowledge
