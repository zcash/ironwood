import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Canonical.LookupRows
import Zcash.Snark.Verifier.Parametric

/-!
# Instantiating lookup constraints with routed decoded polynomials

The verifier names each committed polynomial by `CommitmentId`.  Given a polynomial resolver keyed
by those names, this module constructs polynomial-valued lookup entries whose next/previous fields
are rotations of the same three base polynomials.  A single query-level opening hypothesis over the
verifier's actual `lookupQueries` then proves that evaluating those entries at `x` reproduces
`subProofLookups`.

Everything is parametric in the verification key, proof string, proof index, and resolver.  No
circuit fixture or concrete verification key occurs here.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial

/--
The polynomial feed for one verifier query family.

An `Expr` leaf indexes a query-layout entry, not a committed column directly.  The
entry names a base column and a rotation, so its polynomial is the resolved base
column composed with `ω^rotation · X`.  As in the verifier's `finFn` evaluation
feeds, indices outside the shape-level query count read zero.
-/
def resolverQueryFeed
    {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
    (column : ℕ → CPoly) : ℕ → CPoly :=
  fun query =>
    if _hquery : query < n then
      let entry := layout.getD query (0, 0)
      comp (column entry.1) (C (omega ^ entry.2) * X)
    else 0

/-- An in-range query feed evaluates its resolved column at the rotated point. -/
theorem resolverQueryFeed_eval
    {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
    (column : ℕ → CPoly)
    {query : ℕ} (hquery : query < n) (x : Fp) :
    (resolverQueryFeed (n := n) omega layout column query).eval x =
      (column (layout.getD query (0, 0)).1).eval
        (rotateOmega omega x (layout.getD query (0, 0)).2) := by
  simp only [resolverQueryFeed, dif_pos hquery,
    eval_comp, eval_mul, eval_C, eval_X, rotateOmega]
  rw [_root_.mul_comm]

/-- Outside the shape-level query count the feed is the zero polynomial. -/
theorem resolverQueryFeed_eval_of_ge
    {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
    (column : ℕ → CPoly)
    {query : ℕ} (hquery : n ≤ query) (x : Fp) :
    (resolverQueryFeed (n := n) omega layout column query).eval x = 0 := by
  simp [resolverQueryFeed, Nat.not_lt.mpr hquery]

/--
Uniform openings of a complete `columnQueries` block reconstruct its entire
resolver query feed at the verifier challenge.

The layout-count equality is the only structural premise: `List.ofFn evals`
already has exactly `n` entries. Out-of-range query indices are zero on both
sides, matching `finFn`.
-/
theorem resolverQueryFeed_eval_of_columnQueries
    {n k : ℕ} {G : Type*}
    (omega x : Fp)
    (commitment : ℕ → G) (mkId : ℕ → CommitmentId)
    (layout : List (ℕ × ℤ)) (evals : Fin n → Fp)
    (hlayout : layout.length = n)
    (poly : CommitmentId → CPoly)
    (hopen : ∀ q ∈
      columnQueries (k := k) omega x commitment mkId layout
        (List.ofFn evals),
      (poly q.commId).eval q.point = q.eval)
    (query : ℕ) :
    (resolverQueryFeed (n := n) omega layout
      (fun column => poly (mkId column)) query).eval x =
        finFn evals query := by
  by_cases hquery : query < n
  · have hlayoutQuery : query < layout.length := by
      simpa only [hlayout] using hquery
    let q : VerifierQuery k Fp G :=
      { point := rotateOmega omega x
          (layout.getD query (0, 0)).2
        commitment := .point
          (commitment (layout.getD query (0, 0)).1)
        eval := (List.ofFn evals).getD query 0
        commId := mkId (layout.getD query (0, 0)).1 }
    have hq :
        q ∈ columnQueries (k := k) omega x commitment mkId layout
          (List.ofFn evals) := by
      exact columnQuery_getD_mem omega x commitment mkId layout
        (List.ofFn evals) hlayoutQuery (by simpa using hquery)
    have hopenQuery := hopen q hq
    rw [resolverQueryFeed_eval omega layout _ hquery x]
    simpa [q, finFn, hquery] using hopenQuery
  · rw [resolverQueryFeed_eval_of_ge omega layout _
      (Nat.le_of_not_gt hquery) x]
    simp [finFn, hquery]

/-- Fixed-query polynomials selected from commitment identities and the VK layout. -/
def fixedQueryFeedOfResolver
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly) : ℕ → CPoly :=
  resolverQueryFeed (n := shape.numFixedQueries)
    vk.omega vk.fixedQueryLayout fun column => poly (.fixedCol column)

/-- Advice-query polynomials for one proof, selected from the VK layout. -/
def adviceQueryFeedOfResolver
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : ℕ) : ℕ → CPoly :=
  resolverQueryFeed (n := shape.numAdviceQueries)
    vk.omega vk.adviceQueryLayout fun column => poly (.adviceCol p column)

/-- Instance-query polynomials for one proof, selected from the VK layout. -/
def instanceQueryFeedOfResolver
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → CPoly)
    (p : ℕ) : ℕ → CPoly :=
  resolverQueryFeed (n := shape.numInstanceQueries)
    vk.omega vk.instanceQueryLayout fun column => poly (.instanceCol p column)

/-- One proof's lookup commitments paired with their five claimed evaluations, in verifier order. -/
def subProofLookupCommitments {shape : Shape} {F G : Type*}
    (ps : ProofString shape F G) (p : Fin shape.numProofs) :
    List (LookupCommitments G × LookupEval F) :=
  List.ofFn fun l =>
    ({ product := ps.lookupProduct p l,
       permutedInput := ps.lookupPermutedInput p l,
       permutedTable := ps.lookupPermutedTable p l },
     ps.lookupEvals p l)

/-- The verifier's lookup-only query block for one sub-proof. -/
def subProofLookupQueries {shape : Shape} {F G : Type*} [Field F]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (p : Fin shape.numProofs) :
    List (VerifierQuery shape.k F G) :=
  lookupQueries ch.x (rotateOmega vk.omega ch.x (-1)) (rotateOmega vk.omega ch.x 1)
    (CommitmentId.lookupProduct p) (CommitmentId.lookupPermInput p)
    (CommitmentId.lookupPermTable p) (subProofLookupCommitments ps p)

/-- Every lookup-only query is an actual member of the verifier's complete assembled query list. -/
theorem mem_assembleQueries_of_mem_subProofLookupQueries
    {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (p : Fin shape.numProofs) {q : VerifierQuery shape.k F G}
    (hq : q ∈ subProofLookupQueries vk ps ch p) :
    q ∈ assembleQueries vk instanceCommitment ps ch := by
  have hblock : q ∈ subProofOpeningQueries vk instanceCommitment ps ch.x
      (rotateOmega vk.omega ch.x (-1)) (rotateOmega vk.omega ch.x 1)
      (rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1))) p := by
    exact List.mem_append_right _ (by
      simpa [subProofLookupQueries, subProofLookupCommitments] using hq)
  have hperProof : q ∈ subProofBlocks fun p : Fin shape.numProofs =>
      subProofOpeningQueries vk instanceCommitment ps ch.x
        (rotateOmega vk.omega ch.x (-1)) (rotateOmega vk.omega ch.x 1)
        (rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1))) p := by
    exact List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, hblock⟩
  rw [assembleQueries_parametric_numProofs]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hperProof))

/-- Polynomial lookup entries built from an arbitrary commitment-ID resolver.  Coherence of the
rotations is definitional through `lookupEvalPolys`. -/
def lookupEntriesOfResolver {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : ℕ) :
    List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)) :=
  List.ofFn fun l =>
    (lookupEvalPolys vk.omega
      (poly (.lookupProduct p l))
      (poly (.lookupPermInput p l))
      (poly (.lookupPermTable p l)),
     vk.lookupInputExprs l,
     vk.lookupTableExprs l)

/-- The selected lookup's compressed input polynomial under the resolver-backed column feeds. -/
def lookupInputPolyOfResolver {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) : CPoly :=
  compressExprs
    (fixedQueryFeedOfResolver vk poly)
    (adviceQueryFeedOfResolver vk poly p)
    (instanceQueryFeedOfResolver vk poly p)
    (C ch.theta)
    ((vk.lookupInputExprs l).map (Expr.map C))

theorem lookupInputPolyOfResolver_eq {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) :
    lookupInputPolyOfResolver vk ch poly p l =
      compressExprs
        (fixedQueryFeedOfResolver vk poly)
        (adviceQueryFeedOfResolver vk poly p)
        (instanceQueryFeedOfResolver vk poly p)
        (C ch.theta) ((vk.lookupInputExprs l).map (Expr.map C)) := rfl

/-- The selected lookup's compressed table polynomial under the same resolver-backed feeds. -/
def lookupTablePolyOfResolver {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) : CPoly :=
  compressExprs
    (fixedQueryFeedOfResolver vk poly)
    (adviceQueryFeedOfResolver vk poly p)
    (instanceQueryFeedOfResolver vk poly p)
    (C ch.theta)
    ((vk.lookupTableExprs l).map (Expr.map C))

theorem lookupTablePolyOfResolver_eq {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) :
    lookupTablePolyOfResolver vk ch poly p l =
      compressExprs
        (fixedQueryFeedOfResolver vk poly)
        (adviceQueryFeedOfResolver vk poly p)
        (instanceQueryFeedOfResolver vk poly p)
        (C ch.theta) ((vk.lookupTableExprs l).map (Expr.map C)) := rfl

/-- A full constraint model whose column polynomials and lookup arguments are resolved by stable
commitment identities.  The permutation sets/chunks remain parameters until their analogous
canonical routing layer is installed. -/
def constraintModelOfResolver
    {shape : CircuitShape} {numProofs k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (sets : Fin numProofs → List (PermSetEval CPoly))
    (chunks : Fin numProofs →
      List (PermSetEval CPoly × List (CPoly × CPoly)))
    (l0 lLast lBlind : CPoly) :
    ConstraintPolyModel numProofs where
  fixedCols := fixedQueryFeedOfResolver vk poly
  adviceCols := fun proofIndex =>
    adviceQueryFeedOfResolver vk poly proofIndex
  instanceCols := fun proofIndex =>
    instanceQueryFeedOfResolver vk poly proofIndex
  gates := vk.gates
  sets := sets
  chunks := chunks
  lookups := fun proofIndex =>
    lookupEntriesOfResolver vk poly proofIndex
  beta := ch.beta
  gamma := ch.gamma
  delta := vk.delta
  theta := ch.theta
  chunkLen := vk.chunkLen
  l0 := l0
  lLast := lLast
  lBlind := lBlind

@[simp] theorem constraintModelOfResolver_lookups
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (sets : Fin numProofs → List (PermSetEval (CPoly)))
    (chunks : Fin numProofs →
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (l0 lLast lBlind : CPoly) (p : Fin numProofs) :
    (constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind).lookups p
      = lookupEntriesOfResolver vk poly p := rfl

/-- The selected coherent lookup entry occurs in the resolver-built lookup list. -/
theorem lookupEntry_mem_lookupEntriesOfResolver
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) :
    (lookupEvalPolys vk.omega
        (poly (.lookupProduct p l))
        (poly (.lookupPermInput p l))
        (poly (.lookupPermTable p l)),
      vk.lookupInputExprs l,
      vk.lookupTableExprs l) ∈ lookupEntriesOfResolver vk poly p := by
  exact List.mem_ofFn.mpr ⟨l, rfl⟩

/-- The same selected entry, exposed directly through the full resolver-built model.  This is the
membership fact passed to `ConstraintSatisfaction.lookupStart`, `lookupEnd`,
`lookupProductStep`, `lookupRunStart`, and `lookupRunStep`. -/
theorem lookupEntry_mem_constraintModelOfResolver
    {shape : CircuitShape} {numProofs k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (sets : Fin numProofs → List (PermSetEval CPoly))
    (chunks : Fin numProofs →
      List (PermSetEval CPoly × List (CPoly × CPoly)))
    (l0 lLast lBlind : CPoly)
    (p : Fin numProofs) (l : Fin shape.numLookups) :
    (lookupEvalPolys vk.omega
        (poly (.lookupProduct p l))
        (poly (.lookupPermInput p l))
        (poly (.lookupPermTable p l)),
      vk.lookupInputExprs l,
      vk.lookupTableExprs l) ∈
        (constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind).lookups p :=
  lookupEntry_mem_lookupEntriesOfResolver vk poly p l

private theorem lookup_query_mem {shape : Shape} {F G : Type*} [Field F]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (p : Fin shape.numProofs) (l : Fin shape.numLookups)
    (q : VerifierQuery shape.k F G)
    (hq : q ∈
      [{ point := ch.x,
         commitment := .point (ps.lookupProduct p l),
         eval := (ps.lookupEvals p l).productEval,
         commId := .lookupProduct p l },
       { point := ch.x,
         commitment := .point (ps.lookupPermutedInput p l),
         eval := (ps.lookupEvals p l).permutedInputEval,
         commId := .lookupPermInput p l },
       { point := ch.x,
         commitment := .point (ps.lookupPermutedTable p l),
         eval := (ps.lookupEvals p l).permutedTableEval,
         commId := .lookupPermTable p l },
       { point := rotateOmega vk.omega ch.x (-1),
         commitment := .point (ps.lookupPermutedInput p l),
         eval := (ps.lookupEvals p l).permutedInputInvEval,
         commId := .lookupPermInput p l },
       { point := rotateOmega vk.omega ch.x 1,
         commitment := .point (ps.lookupProduct p l),
         eval := (ps.lookupEvals p l).productNextEval,
         commId := .lookupProduct p l }]) :
    q ∈ subProofLookupQueries vk ps ch p := by
  rw [subProofLookupQueries, lookupQueries, List.mem_flatMap]
  refine ⟨(
    ({ product := ps.lookupProduct p l,
       permutedInput := ps.lookupPermutedInput p l,
       permutedTable := ps.lookupPermutedTable p l },
     ps.lookupEvals p l), (l : ℕ)), ?_, ?_⟩
  · rw [List.mem_iff_getElem]
    refine ⟨l, ?_, ?_⟩
    · simp [subProofLookupCommitments]
    · simp [subProofLookupCommitments]
  · simpa [subProofLookupCommitments] using hq

/-- **Generic lookup polynomial routing.** If the polynomial selected by every lookup query's
`CommitmentId` takes the query's claimed value at its opened point, evaluating the coherent
polynomial-valued lookup entries at `x` gives exactly the verifier's `subProofLookups`.

The hypothesis is deliberately query-shaped: multiopen extraction can supply it uniformly, and the
two queries sharing the product ID (respectively permuted-input ID) automatically use the same
polynomial. -/
theorem eval_lookupEntriesOfResolver {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (poly : CommitmentId → CPoly)
    (p : Fin shape.numProofs)
    (hopen : ∀ q ∈ subProofLookupQueries vk ps ch p,
      (poly q.commId).eval q.point = q.eval) :
    (lookupEntriesOfResolver vk poly p).map
        (fun lk => (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2))
      = subProofLookups vk ps p := by
  rw [lookupEntriesOfResolver, subProofLookups, List.map_ofFn]
  congr 1
  funext l
  have hproduct := hopen
    { point := ch.x,
      commitment := .point (ps.lookupProduct p l),
      eval := (ps.lookupEvals p l).productEval,
      commId := .lookupProduct p l }
    (lookup_query_mem vk ps ch p l _ (by simp))
  have hinput := hopen
    { point := ch.x,
      commitment := .point (ps.lookupPermutedInput p l),
      eval := (ps.lookupEvals p l).permutedInputEval,
      commId := .lookupPermInput p l }
    (lookup_query_mem vk ps ch p l _ (by simp))
  have htable := hopen
    { point := ch.x,
      commitment := .point (ps.lookupPermutedTable p l),
      eval := (ps.lookupEvals p l).permutedTableEval,
      commId := .lookupPermTable p l }
    (lookup_query_mem vk ps ch p l _ (by simp))
  have hinputInv := hopen
    { point := rotateOmega vk.omega ch.x (-1),
      commitment := .point (ps.lookupPermutedInput p l),
      eval := (ps.lookupEvals p l).permutedInputInvEval,
      commId := .lookupPermInput p l }
    (lookup_query_mem vk ps ch p l _ (by simp))
  have hproductNext := hopen
    { point := rotateOmega vk.omega ch.x 1,
      commitment := .point (ps.lookupProduct p l),
      eval := (ps.lookupEvals p l).productNextEval,
      commId := .lookupProduct p l }
    (lookup_query_mem vk ps ch p l _ (by simp))
  have hproduct' :
      (poly (.lookupProduct p l)).eval ch.x = (ps.lookupEvals p l).productEval := by
    simpa using hproduct
  have hproductNext' :
      ((poly (.lookupProduct p l)).comp (C vk.omega * X)).eval ch.x
        = (ps.lookupEvals p l).productNextEval := by
    rw [eval_comp_rotate, _root_.mul_comm vk.omega ch.x]
    simpa only [rotateOmega, zpow_one] using hproductNext
  have hinput' :
      (poly (.lookupPermInput p l)).eval ch.x
        = (ps.lookupEvals p l).permutedInputEval := by
    simpa using hinput
  have hinputInv' :
      ((poly (.lookupPermInput p l)).comp (C vk.omega⁻¹ * X)).eval ch.x
        = (ps.lookupEvals p l).permutedInputInvEval := by
    rw [eval_comp_rotate, _root_.mul_comm vk.omega⁻¹ ch.x]
    simpa only [rotateOmega, zpow_neg_one] using hinputInv
  have htable' :
      (poly (.lookupPermTable p l)).eval ch.x
        = (ps.lookupEvals p l).permutedTableEval := by
    simpa using htable
  apply Prod.ext
  · simp only [Function.comp_apply, LookupEval.map, lookupEvalPolys]
    simp only [hproduct', hproductNext', hinput', hinputInv', htable']
  · rfl

/-- The same routing theorem with its opening premise supplied on the verifier's complete assembled
query list. -/
theorem eval_lookupEntriesOfResolver_of_assembleQueries
    {shape : Shape} {G : Type*} [Inhabited G]
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly) (p : Fin shape.numProofs)
    (hopen : ∀ q ∈ assembleQueries vk instanceCommitment ps ch,
      (poly q.commId).eval q.point = q.eval) :
    (lookupEntriesOfResolver vk poly p).map
        (fun lk => (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2))
      = subProofLookups vk ps p := by
  apply eval_lookupEntriesOfResolver vk ps ch poly p
  intro q hq
  exact hopen q (mem_assembleQueries_of_mem_subProofLookupQueries
    vk instanceCommitment ps ch p hq)

/-- The resolver-built model discharges the existing `hlookups` bridge from one uniform
query-opening fact per sub-proof. -/
theorem eval_constraintModelOfResolver_lookups {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (poly : CommitmentId → CPoly)
    (sets : Fin shape.numProofs → List (PermSetEval (CPoly)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (l0 lLast lBlind : CPoly)
    (hopen : ∀ p q, q ∈ subProofLookupQueries vk ps ch p →
      (poly q.commId).eval q.point = q.eval) :
    ∀ p, ((constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind).lookups p).map
        (fun lk => (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2))
      = subProofLookups vk ps p :=
  fun p => eval_lookupEntriesOfResolver vk ps ch poly p (hopen p)

/-- The model-level `hlookups` bridge from one opening fact over the verifier's complete query
list. -/
theorem eval_constraintModelOfResolver_lookups_of_assembleQueries
    {shape : Shape} {G : Type*} [Inhabited G]
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (sets : Fin shape.numProofs → List (PermSetEval (CPoly)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (l0 lLast lBlind : CPoly)
    (hopen : ∀ q ∈ assembleQueries vk instanceCommitment ps ch,
      (poly q.commId).eval q.point = q.eval) :
    ∀ p, ((constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind).lookups p).map
        (fun lk => (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2))
      = subProofLookups vk ps p :=
  fun p => eval_lookupEntriesOfResolver_of_assembleQueries
    vk instanceCommitment ps ch poly p hopen

/-- Full family satisfaction specialized to one resolver-built lookup gives exactly the five
coherent divisibility facts consumed by `deployed_lookup_subset`. -/
theorem ConstraintSatisfaction.lookupConstraintsDvdOfResolver
    {shape : CircuitShape} {numProofs k : ℕ} {G : Type*} {n : ℕ}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (sets : Fin numProofs → List (PermSetEval CPoly))
    (chunks : Fin numProofs →
      List (PermSetEval CPoly × List (CPoly × CPoly)))
    (l0 lLast lBlind : CPoly)
    (h : ConstraintSatisfaction
      (constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind) n)
    (p : Fin numProofs) (l : Fin shape.numLookups) :
    LookupConstraintsDvd n vk.omega ch.beta ch.gamma
      (poly (.lookupProduct p l))
      (poly (.lookupPermInput p l))
      (poly (.lookupPermTable p l))
      (lookupInputPolyOfResolver vk ch poly p l)
      (lookupTablePolyOfResolver vk ch poly p l)
      l0 lLast lBlind := by
  let lk :
      LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp) :=
    (lookupEvalPolys vk.omega
        (poly (.lookupProduct p l))
        (poly (.lookupPermInput p l))
        (poly (.lookupPermTable p l)),
      vk.lookupInputExprs l,
      vk.lookupTableExprs l)
  have hlk : lk ∈
      (constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind).lookups p := by
    exact lookupEntry_mem_constraintModelOfResolver
      vk ch poly sets chunks l0 lLast lBlind p l
  constructor
  · simpa [lk, constraintModelOfResolver, lookupEvalPolys] using h.lookupStart p hlk
  · simpa [lk, constraintModelOfResolver, lookupEvalPolys] using h.lookupEnd p hlk
  · simpa only [lk, constraintModelOfResolver, lookupEvalPolys,
      lookupInputPolyOfResolver_eq, lookupTablePolyOfResolver_eq] using
      h.lookupProductStep p hlk
  · simpa [lk, constraintModelOfResolver, lookupEvalPolys] using h.lookupRunStart p hlk
  · simpa only [lk, constraintModelOfResolver, lookupEvalPolys] using h.lookupRunStep p hlk

end Zcash.Snark
