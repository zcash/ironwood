import Zcash.Circuits.Integration.FixedColumns
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.TopLevelLookups

/-!
# Lookup selector rows

Lookup projection only needs packed-selector values for selector leaves that occur
in the selected lookup's input expressions. Unrelated gate selectors may legitimately
be active at the same absolute row.

This module separates the proof-independent dense-row fact from the proof-dependent
fixed-polynomial binding step. The latter transports exact packed rows into the
resolver environment, preserving the caller's existing commitment-relation branch.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial

set_option maxHeartbeats 20000

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [Inhabited G]

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/-- A structural predicate over exactly the selector leaves of an expression. -/
def ExpressionSelectorLeavesSatisfy
    {F : Type} (predicate : Selector → Prop) :
    Expression F Query → Prop
  | .var (.selector selector) => predicate selector
  | .var _ => True
  | .const _ => True
  | .add left right =>
      ExpressionSelectorLeavesSatisfy predicate left ∧
        ExpressionSelectorLeavesSatisfy predicate right
  | .mul left right =>
      ExpressionSelectorLeavesSatisfy predicate left ∧
        ExpressionSelectorLeavesSatisfy predicate right

def decideExpressionSelectorLeavesSatisfy
    {F : Type} (predicate : Selector → Prop)
    [DecidablePred predicate] :
    (expression : Expression F Query) →
      Decidable (ExpressionSelectorLeavesSatisfy predicate expression)
  | .var (.selector selector) =>
      show Decidable (predicate selector) from inferInstance
  | .var (.fixed _ _) => isTrue trivial
  | .var (.advice _ _) => isTrue trivial
  | .var (.instance _ _) => isTrue trivial
  | .const _ => isTrue trivial
  | .add left right =>
      @instDecidableAnd
        (ExpressionSelectorLeavesSatisfy predicate left)
        (ExpressionSelectorLeavesSatisfy predicate right)
        (decideExpressionSelectorLeavesSatisfy predicate left)
        (decideExpressionSelectorLeavesSatisfy predicate right)
  | .mul left right =>
      @instDecidableAnd
        (ExpressionSelectorLeavesSatisfy predicate left)
        (ExpressionSelectorLeavesSatisfy predicate right)
        (decideExpressionSelectorLeavesSatisfy predicate left)
        (decideExpressionSelectorLeavesSatisfy predicate right)

instance expressionSelectorLeavesSatisfyDecidable
    {F : Type} (predicate : Selector → Prop)
    [DecidablePred predicate] (expression : Expression F Query) :
    Decidable (ExpressionSelectorLeavesSatisfy predicate expression) :=
  decideExpressionSelectorLeavesSatisfy predicate expression

/-- A pointwise stronger selector-leaf property implies a weaker one. -/
theorem ExpressionSelectorLeavesSatisfy.mono
    {F : Type} {first second : Selector → Prop}
    {expression : Expression F Query}
    (h : ExpressionSelectorLeavesSatisfy first expression)
    (hmono : ∀ selector, first selector → second selector) :
    ExpressionSelectorLeavesSatisfy second expression := by
  induction expression with
  | var query =>
      cases query with
      | selector selector =>
          exact hmono selector h
      | fixed column rotation =>
          trivial
      | advice column rotation =>
          trivial
      | «instance» column rotation =>
          trivial
  | const value =>
      trivial
  | add left right ihLeft ihRight =>
      exact ⟨ihLeft h.1, ihRight h.2⟩
  | mul left right ihLeft ihRight =>
      exact ⟨ihLeft h.1, ihRight h.2⟩

/-- Every selector leaf belongs to the expression's syntactic leaf list. -/
private theorem ExpressionSelectorLeavesSatisfy.mem_expressionSelectorLeaves
    {F : Type} (expression : Expression F Query) :
    ExpressionSelectorLeavesSatisfy
      (fun selector =>
        selector ∈ EnabledLookup.expressionSelectorLeaves expression)
      expression := by
  induction expression with
  | var query =>
      cases query <;>
        simp [ExpressionSelectorLeavesSatisfy,
          EnabledLookup.expressionSelectorLeaves]
  | const value =>
      trivial
  | add left right ihLeft ihRight
  | mul left right ihLeft ihRight =>
      constructor
      · exact ihLeft.mono fun selector hselector => by
          simp only [EnabledLookup.expressionSelectorLeaves,
            List.mem_append]
          exact Or.inl hselector
      · exact ihRight.mono fun selector hselector => by
          simp only [EnabledLookup.expressionSelectorLeaves,
            List.mem_append]
          exact Or.inr hselector

/-- Every selector leaf of an input expression occurs in the lookup's leaf list. -/
theorem EnabledLookup.expressionSelectorLeaves_mem_inputSelectorLeaves
    (lookup : EnabledLookup Fp)
    {expression : Expression Fp Query}
    (hexpression : expression ∈ lookup.argument.inputs) :
    ExpressionSelectorLeavesSatisfy
      (fun selector => selector ∈ lookup.inputSelectorLeaves) expression := by
  have hsubset :
      ∀ selector ∈ EnabledLookup.expressionSelectorLeaves expression,
        selector ∈ lookup.inputSelectorLeaves := by
    intro selector hselector
    simp only [EnabledLookup.inputSelectorLeaves, List.mem_flatMap]
    exact
      ⟨expression, hexpression, hselector⟩
  exact
    (ExpressionSelectorLeavesSatisfy.mem_expressionSelectorLeaves
      expression).mono hsubset

/--
Agreement on the selector leaves occurring in an expression is sufficient for
selector substitution to agree with a concrete selector valuation.
-/
theorem expression_eval_substValuation_eq_queryEval_of_selectorLeaves
    (map : SelCompressMap) (environment : Environment Fp)
    (selectors : ℕ → Fp) (row : ℤ)
    (expression : Expression Fp Query)
    (hagrees :
      ExpressionSelectorLeavesSatisfy (fun selector =>
        substValuation map.lookup
            (Query.eval environment (fun _ => 0) row)
            (.selector selector) =
          selectors selector.index) expression) :
    expression.eval
        (substValuation map.lookup
          (Query.eval environment (fun _ => 0) row)) =
      expression.eval
        (Query.eval environment selectors row) := by
  revert hagrees
  induction expression with
  | var query =>
      intro hagrees
      cases query with
      | selector selector =>
          exact hagrees
      | fixed column rotation =>
          rfl
      | advice column rotation =>
          rfl
      | «instance» column rotation =>
          rfl
  | const value =>
      intro hagrees
      rfl
  | add left right ihLeft ihRight =>
      intro hagrees
      exact congrArg₂ (· + ·)
        (ihLeft hagrees.1) (ihRight hagrees.2)
  | mul left right ihLeft ihRight =>
      intro hagrees
      exact congrArg₂ (· * ·)
        (ihLeft hagrees.1) (ihRight hagrees.2)

/--
Proof-independent dense-row selector facts, restricted to selector leaves that
actually occur in this lookup's input expressions.

The intended structural source is the selector compiler: lookup inputs contain only
complex selectors, selector kinds are consistent by allocated index, degree-zero
selectors receive singleton packed columns, and V1 placement isolates their activation
rows. Until those compiler laws are exposed, a concrete circuit may certify this small
finite property directly.
-/
def EnabledLookup.InputSelectorLeafRowsExact
    (top : TopLevelCircuit Fp Config PublicInput)
    (rows : ℕ → List Fp) (lookup : EnabledLookup Fp) : Prop :=
  lookup.argument.inputs.Forall fun expression =>
    ExpressionSelectorLeavesSatisfy (fun selector =>
      match top.selectorMap.lookup selector.index with
      | none =>
          lookup.selectorValue selector.index = 0
      | some compressed =>
          compressed.packedCol < top.pinnedCS.numFixedColumns ∧
            (selReplacement compressed).eval
                (fun
                  | .fixed column _ =>
                      (rows column.index).getD
                        (top.placement lookup.region + lookup.row) 0
                  | _ => 0) =
              lookup.selectorValue selector.index) expression

private theorem selReplacement_eval_of_singleton
    (compressed : SelCompress) (valuation : Query → Fp)
    (hlength : compressed.combinationLen = 1)
    (hroot : compressed.assignedRoot = 1) :
    (selReplacement compressed).eval valuation =
      valuation (.fixed ⟨compressed.packedCol⟩ 0) := by
  rcases compressed with ⟨column, length, root⟩
  simp only at hlength hroot
  subst length
  subst root
  rfl

/--
Realizing the lookup-selector entries in the shared fixed boundary supplies the exact
dense-row selector valuation used by lookup projection.

The explicitly interim required-entry list contains an out-of-bounds sentinel if a
relevant selector is absent from the compression map or is not packed as a singleton
at root one. Thus any `realizes` proof rules those cases out without exposing a
separate concrete-circuit premise. The structural replacement proves singleton
packing and disabled-row zero directly from compiler invariants.
-/
theorem EnabledLookup.inputSelectorLeafRowsExact_of_realizes
    (top : TopLevelCircuit Fp Config PublicInput)
    (rows : ℕ → List Fp) (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups (top.operations) 0)
    (realizes : ∀ column row value,
      (column, row, value) ∈ topLevelRequiredFixedEntries top →
        column < top.pinnedCS.numFixedColumns ∧
          (rows column).getD row 0 = (value : Fp)) :
    lookup.InputSelectorLeafRowsExact top rows := by
  rw [EnabledLookup.InputSelectorLeafRowsExact,
    List.forall_iff_forall_mem]
  intro expression hexpression
  have hmembers :=
    lookup.expressionSelectorLeaves_mem_inputSelectorLeaves hexpression
  apply hmembers.mono
  intro selector hselectorLeaf
  have required_of_result
      (entry : ℕ × ℕ × ℕ)
      (hresult :
        (match top.selectorMap.lookup selector.index with
        | some compressed =>
            if compressed.combinationLen = 1 ∧
                compressed.assignedRoot = 1 then
              some
                (compressed.packedCol,
                  top.regionStarts.getD lookup.region 0 + lookup.row,
                  if lookup.enabled.any
                      (fun candidate =>
                        candidate.index == selector.index) then
                    1
                  else
                    0)
            else
              some
                (top.pinnedCS.numFixedColumns,
                  top.regionStarts.getD lookup.region 0 + lookup.row, 0)
        | none =>
            some
              (top.pinnedCS.numFixedColumns,
                top.regionStarts.getD lookup.region 0 + lookup.row, 0)) =
          some entry) :
      entry ∈ topLevelRequiredFixedEntries top := by
    simp only [topLevelRequiredFixedEntries]
    apply List.mem_append_right
    simp only [topLevelSingletonLookupSelectorEntries,
      List.mem_flatMap]
    refine ⟨lookup, henabled, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨selector, hselectorLeaf, hresult⟩
  cases hlookup : top.selectorMap.lookup selector.index with
  | none =>
      have hrequired :=
        required_of_result
          (top.pinnedCS.numFixedColumns,
            top.regionStarts.getD lookup.region 0 + lookup.row, 0)
          (by simp [hlookup])
      have hbound :=
        (realizes top.pinnedCS.numFixedColumns
          (top.regionStarts.getD lookup.region 0 + lookup.row)
          0 hrequired).1
      exact False.elim (Nat.lt_irrefl _ hbound)
  | some compressed =>
      by_cases hsingleton :
          compressed.combinationLen = 1 ∧
            compressed.assignedRoot = 1
      · let expected :=
          if lookup.enabled.any
              (fun candidate =>
                candidate.index == selector.index) then
            1
          else
            0
        have hrequired :=
          required_of_result
            (compressed.packedCol,
              top.regionStarts.getD lookup.region 0 + lookup.row,
              expected)
            (by simp [hlookup, hsingleton, expected])
        have hrealized :=
          realizes compressed.packedCol
            (top.regionStarts.getD lookup.region 0 + lookup.row)
            expected hrequired
        refine ⟨hrealized.1, ?_⟩
        rw [selReplacement_eval_of_singleton compressed _
          hsingleton.1 hsingleton.2]
        by_cases henabledSelector :
            ∃ candidate ∈ lookup.enabled,
              candidate.index = selector.index
        · have hany :
              lookup.enabled.any
                  (fun candidate =>
                    candidate.index == selector.index) = true := by
            simp only [List.any_eq_true, beq_iff_eq]
            exact henabledSelector
          have hvalue := hrealized.2
          simp only [expected, hany, if_true, Nat.cast_one] at hvalue
          simp only [hvalue, TopLevelCircuit.placement_apply,
            EnabledLookup.selectorValue, henabledSelector, if_true]
        · have hany :
              lookup.enabled.any
                  (fun candidate =>
                    candidate.index == selector.index) = false := by
            simp only [List.any_eq_false]
            intro candidate hcandidate
            exact fun heq =>
              henabledSelector
                ⟨candidate, hcandidate, beq_iff_eq.mp heq⟩
          have hvalue := hrealized.2
          simp only [expected, hany, Bool.false_eq_true, if_false,
            Nat.cast_zero] at hvalue
          simp only [hvalue, TopLevelCircuit.placement_apply,
            EnabledLookup.selectorValue, henabledSelector, if_false]
      · have hrequired :=
          required_of_result
            (top.pinnedCS.numFixedColumns,
              top.regionStarts.getD lookup.region 0 + lookup.row, 0)
            (by simp [hlookup, hsingleton])
        have hbound :=
          (realizes top.pinnedCS.numFixedColumns
            (top.regionStarts.getD lookup.region 0 + lookup.row)
            0 hrequired).1
        exact False.elim (Nat.lt_irrefl _ hbound)

instance EnabledLookup.inputSelectorLeafRowsExactDecidable
    (top : TopLevelCircuit Fp Config PublicInput)
    (rows : ℕ → List Fp) (lookup : EnabledLookup Fp) :
    Decidable (lookup.InputSelectorLeafRowsExact top rows) := by
  let predicate : Selector → Prop := fun selector =>
    match top.selectorMap.lookup selector.index with
    | none =>
        lookup.selectorValue selector.index = 0
    | some compressed =>
        compressed.packedCol < top.pinnedCS.numFixedColumns ∧
          (selReplacement compressed).eval
              (fun
                | .fixed column _ =>
                    (rows column.index).getD
                      (top.placement lookup.region + lookup.row) 0
                | _ => 0) =
            lookup.selectorValue selector.index
  change Decidable (lookup.argument.inputs.Forall fun expression =>
    ExpressionSelectorLeavesSatisfy predicate expression)
  haveI : DecidablePred predicate := fun selector => by
    dsimp only [predicate]
    split <;> infer_instance
  infer_instance

omit [AddCommGroup G] [Module Fp G] [Inhabited G] in
private theorem resolverFixedRead_of_rowPolynomial
    {shape : Shape} (urs : URS G)
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (rows : ℕ → List Fp)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) => vk.omega ^ (i : ℕ))
    (proofIndex : Fin shape.numProofs) (usableRows column row : ℕ)
    (hrow : row < 2 ^ urs.k)
    (hpolynomial :
      poly (.fixedCol column) =
        instanceRowPolynomial (2 ^ urs.k) vk.omega (rows column)) :
    (resolverEnvironment vk poly proofIndex usableRows).fixed
        ⟨column⟩ row =
      (rows column).getD row 0 := by
  rw [resolverEnvironment_fixed, hpolynomial]
  simpa using instanceRowPolynomial_eval hrows ⟨row, hrow⟩

omit [Module Fp G] in
/--
Relevant exact packed rows and fixed-polynomial binding recover precisely the
expression-level selector boundary consumed by lookup projection.
-/
def EnabledLookup.inputSelectorValuesRealized_or_bad
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    (poly : CommitmentId → CPoly)
    (rows : ℕ → List Fp)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ))
    (hn : (top.toVerifierKey pp urs).n = 2 ^ urs.k)
    {Bad : Type}
    (binding : ∀ column,
      column < top.pinnedCS.numFixedColumns →
        poly (.fixedCol column) =
            instanceRowPolynomial (2 ^ urs.k)
              (top.toVerifierKey pp urs).omega (rows column) ⊕'
          Bad)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (lookup : EnabledLookup Fp)
    (hrow :
      top.placement lookup.region + lookup.row <
        (top.toVerifierKey pp urs).n)
    (hexact : lookup.InputSelectorLeafRowsExact top rows) :
    lookup.InputSelectorValuesRealized top
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)) ⊕'
      Bad :=
  bindOrRelationWitness
    (boundedForallOrRelationWitness (n := top.pinnedCS.numFixedColumns) binding)
    fun hbinding => by
    classical
    intro expression hexpression
    apply expression_eval_substValuation_eq_queryEval_of_selectorLeaves
    apply
      (List.forall_iff_forall_mem.mp hexact
        expression hexpression).mono
    intro selector hstatic
    cases hcompressed :
        top.selectorMap.lookup selector.index with
    | none =>
        rw [hcompressed] at hstatic
        simpa [Halo2.substValuation, hcompressed, Query.eval] using
          hstatic.symm
    | some compressed =>
        rw [hcompressed] at hstatic
        obtain ⟨hcolumn, hstatic⟩ := hstatic
        have hpolynomial := hbinding compressed.packedCol hcolumn
        have hdomainRow :
            top.placement lookup.region + lookup.row < 2 ^ urs.k := by
          rwa [← hn]
        have hfixed :
            (resolverEnvironment
                (top.toVerifierKey pp urs) poly proofIndex
                (top.usableRowsAt top.domainExponent)).fixed
                ⟨compressed.packedCol⟩
                (top.placement lookup.region + lookup.row : ℕ) =
              (rows compressed.packedCol).getD
                (top.placement lookup.region + lookup.row) 0 := by
          exact resolverFixedRead_of_rowPolynomial
            urs (top.toVerifierKey pp urs) poly rows hrows proofIndex
            (top.usableRowsAt top.domainExponent) compressed.packedCol
            (top.placement lookup.region + lookup.row)
            hdomainRow hpolynomial
        rw [Halo2.substValuation, hcompressed]
        change
          (selReplacement compressed).eval
              (Query.eval
                (resolverEnvironment
                  (top.toVerifierKey pp urs) poly proofIndex
                  (top.usableRowsAt top.domainExponent))
                (fun _ => 0)
                (top.placement lookup.region + lookup.row)) =
            lookup.selectorValue selector.index
        rw [selReplacement_eval]
        rw [selReplacement_eval] at hstatic
        have hfixed' :
            (resolverEnvironment
                (top.toVerifierKey pp urs) poly proofIndex
                (top.usableRowsAt top.domainExponent)).fixed
                ⟨compressed.packedCol⟩
                ((top.placement lookup.region : ℤ) +
                  (lookup.row : ℤ) + 0) =
              (rows compressed.packedCol).getD
                (top.placement lookup.region + lookup.row) 0 := by
          simpa only [Int.natCast_add, _root_.add_zero] using hfixed
        simpa only [Query.eval, hfixed'] using hstatic

end Zcash.Snark
