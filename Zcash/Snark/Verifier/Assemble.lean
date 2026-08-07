import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Data.List.GetD
import Zcash.Snark.Core.ProofString
import Zcash.Snark.Core.Challenges
import Zcash.Snark.Verifier.Checks
import Zcash.Snark.Verifier.Queries
import Zcash.Snark.Verifier.Expressions
import Zcash.Snark.Verifier.Ipa
import Zcash.Snark.Verifier.Key

/-!
# Assembling the fingerprint MSM

The Lean image of the interactive verifier: a pure function of the proof string, the challenges,
and the verifying-key–level circuit structure, composed in the exact order of halo2
`plonk/verifier.rs`. Three stages:

* `assembleQueries` — recompute the vanishing `h` commitment and `expected_h_eval`, then build the
  ordered opening-query list (per sub-proof: instance, advice, permutation, lookups; then shared:
  fixed, permutation-common, vanishing).
* `constructIntermediateSets` — group that flat list into per-point-set commitment and evaluation
  data. VK-fixed bookkeeping, re-derived in Lean rather than supplied, and exercised by the
  `native_decide` fingerprint match.
* `assembleFinalMsm` — the multiopen `x₁` compression and `x₄` collapse, then the IPA fold,
  producing the final MSM.

`VerifyingKey` is circuit-fixed and supplied as input. The instance commitments are
statement-derived — the verifier computes them from the public instances — and bundled here for
the assembly.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.zero)

/-- View a `Fin n`-indexed family as a total `ℕ`-indexed function, `0` outside range (the query indices
the verifier uses are always in range). -/
def finFn {F : Type*} [Zero F] {n : ℕ} (f : Fin n → F) : ℕ → F :=
  fun i => if h : i < n then f ⟨i, h⟩ else 0

/-- View a `Fin n`-indexed family of group elements as a total `ℕ`-indexed function (`default`
out of range), like `finFn`. Caveat: an out-of-range index aliases `default` rather than erroring
— the Vesta identity in the concrete fixtures, and `0` in abstract shape fixtures — so faithfulness
rests on the VK's query indices being in range. -/
def finFnG {G : Type*} [Inhabited G] {n : ℕ} (f : Fin n → G) : ℕ → G :=
  fun i => if h : i < n then f ⟨i, h⟩ else default

/-- The `i`-th Lagrange basis polynomial of the size-`n` multiplicative domain, evaluated at `x` (halo2
`EvaluationDomain::l_i_range`): `(xⁿ − 1) · ωⁱ / (n · (x − ωⁱ))`. -/
def lagrangeBasisValue {F : Type*} [Field F] (omega : F) (n : ℕ) (xn x : F) (i : ℤ) : F :=
  (xn - 1) * omega ^ i / ((n : F) * (x - omega ^ i))

/-- The three Lagrange basis values the vanishing check needs (halo2 `plonk/verifier.rs`): `l₀`
(rotation `0`), `l_last` (rotation `−(blinding+1)`), and `l_blind` (sum over rotations `−blinding..−1`). -/
def lagrangeBasis {F : Type*} [Field F] (omega : F) (n blinding : ℕ) (xn x : F) : F × F × F :=
  let l0 := lagrangeBasisValue omega n xn x 0
  let lLast := lagrangeBasisValue omega n xn x (-((blinding : ℤ) + 1))
  let lBlind := ((List.range blinding).map
    (fun j => lagrangeBasisValue omega n xn x (-((j : ℤ) + 1)))).foldl (· + ·) (0 : F)
  (l0, lLast, lBlind)

/-- The constraint values for one sub-proof (halo2 `plonk/verifier.rs`, the per-proof `flat_map`):
the gate-polynomial values, then the permutation-argument values, then the lookup-argument values. -/
def subProofExpressions {shape : Shape} {F G : Type*} [Field F] (vk : VerifyingKey shape F G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) (l0 lLast lBlind : F)
    (p : Fin shape.numProofs) : List F :=
  let fE := finFn ps.fixedEvals
  let aE := finFn (ps.adviceEvals p)
  let iE := finFn (ps.instanceEvals p)
  let gateE := vk.gates.map (fun g => g.eval fE aE iE)
  let sets := List.ofFn (fun s => ps.permutationSetEvals p s)
  let chunks := (sets.zip vk.permutationChunks).map (fun sc =>
    (sc.1, sc.2.map (fun cr => (cr.1.resolve iE aE fE, finFn ps.permutationCommonEvals cr.2))))
  let permE := permutationExpressions sets chunks ch.beta ch.gamma ch.x vk.delta vk.chunkLen l0 lLast lBlind
  let lookupE := (List.ofFn (fun l => lookupExpressions (ps.lookupEvals p l)
    (vk.lookupInputExprs l) (vk.lookupTableExprs l) fE aE iE ch.theta ch.beta ch.gamma l0 lLast lBlind)).flatten
  gateE ++ permE ++ lookupE

/-- All constraint values across the sub-proofs, in the verifier's order. -/
def allExpressions {shape : Shape} {F G : Type*} [Field F] (vk : VerifyingKey shape F G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) (l0 lLast lBlind : F) : List F :=
  (List.ofFn (fun p => subProofExpressions vk ps ch l0 lLast lBlind p)).flatten

/-- One sub-proof's permutation set evaluations, in verifier order. -/
def subProofPermSets {shape : Shape} {F G : Type*} [Field F] (ps : ProofString shape F G)
    (p : Fin shape.numProofs) : List (PermSetEval F) :=
  List.ofFn (fun s => ps.permutationSetEvals p s)

/-- One sub-proof's permutation chunks: each set paired with its columns' `(columnEval, permEval)`
list, the column evaluations resolved through the verifying key's chunk layout. -/
def subProofPermChunks {shape : Shape} {F G : Type*} [Field F] (vk : VerifyingKey shape F G)
    (ps : ProofString shape F G) (p : Fin shape.numProofs) :
    List (PermSetEval F × List (F × F)) :=
  ((subProofPermSets ps p).zip vk.permutationChunks).map (fun sc =>
    (sc.1, sc.2.map (fun cr =>
      (cr.1.resolve (finFn (ps.instanceEvals p)) (finFn (ps.adviceEvals p)) (finFn ps.fixedEvals),
        finFn ps.permutationCommonEvals cr.2))))

/-- One sub-proof's lookups: each lookup's evaluations paired with its input and table expressions. -/
def subProofLookups {shape : Shape} {F G : Type*} [Field F] (vk : VerifyingKey shape F G)
    (ps : ProofString shape F G) (p : Fin shape.numProofs) :
    List (LookupEval F × List (Expr F) × List (Expr F)) :=
  List.ofFn (fun l => (ps.lookupEvals p l, vk.lookupInputExprs l, vk.lookupTableExprs l))

/-- The verifier's constraint values for one sub-proof are the generic builder at its own claimed
evaluations. -/
theorem subProofExpressions_eq {shape : Shape} {F G : Type*} [Field F]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (l0 lLast lBlind : F) (p : Fin shape.numProofs) :
    subProofExpressions vk ps ch l0 lLast lBlind p
      = subProofConstraints (finFn ps.fixedEvals) (finFn (ps.adviceEvals p))
          (finFn (ps.instanceEvals p)) vk.gates (subProofPermSets ps p) (subProofPermChunks vk ps p)
          (subProofLookups vk ps p) ch.beta ch.gamma ch.x vk.delta ch.theta vk.chunkLen
          l0 lLast lBlind := by
  simp [subProofExpressions, subProofConstraints, subProofPermSets, subProofPermChunks,
    subProofLookups, List.map_ofFn, Function.comp_def]

/-- The verifier's whole constraint list is the generic builder at its own claimed evaluations. -/
theorem allExpressions_eq {shape : Shape} {F G : Type*} [Field F]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (l0 lLast lBlind : F) :
    allExpressions vk ps ch l0 lLast lBlind
      = allConstraints (finFn ps.fixedEvals) (fun p => finFn (ps.adviceEvals p))
          (fun p => finFn (ps.instanceEvals p)) vk.gates (subProofPermSets ps)
          (subProofPermChunks vk ps) (subProofLookups vk ps) ch.beta ch.gamma ch.x vk.delta
          ch.theta vk.chunkLen l0 lLast lBlind := by
  simp [allExpressions, allConstraints, subProofExpressions_eq]

/-- The verifier's full ordered list of opening queries (halo2 `plonk/verifier.rs`): recompute the
vanishing `h` commitment and `expected_h_eval`, then chain, per sub-proof, the instance / advice /
permutation / lookup queries, followed by the shared fixed / permutation-common / vanishing queries. -/
def assembleQueries {shape : Shape} {F G : Type*} [Field F] [Inhabited G] (vk : VerifyingKey shape F G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) : List (VerifierQuery shape.k F G) :=
  let x := ch.x
  let xn := x ^ vk.n
  let xNext := rotateOmega vk.omega x 1
  let xInv := rotateOmega vk.omega x (-1)
  let xLast := rotateOmega vk.omega x (-((vk.blindingFactors : ℤ) + 1))
  let lb := lagrangeBasis vk.omega vk.n vk.blindingFactors xn x
  let exprs := allExpressions vk ps ch lb.1 lb.2.1 lb.2.2
  let eHEval := expectedHEval exprs ch.y xn
  let hComm := vanishingHCommitment shape.k xn (List.ofFn ps.hPieces)
  let perProof := (List.ofFn (fun p =>
    columnQueries vk.omega x (instanceCommitment p) (CommitmentId.instanceCol p)
        vk.instanceQueryLayout (List.ofFn (ps.instanceEvals p))
    ++ columnQueries vk.omega x (finFnG (ps.adviceCommitments p)) (CommitmentId.adviceCol p)
        vk.adviceQueryLayout (List.ofFn (ps.adviceEvals p))
    ++ permutationQueries x xNext xLast (CommitmentId.permProduct p)
        (List.ofFn (fun s => (ps.permutationProduct p s, ps.permutationSetEvals p s)))
    ++ lookupQueries x xInv xNext (CommitmentId.lookupProduct p) (CommitmentId.lookupPermInput p)
        (CommitmentId.lookupPermTable p) (List.ofFn (fun l =>
        ({ product := ps.lookupProduct p l, permutedInput := ps.lookupPermutedInput p l,
           permutedTable := ps.lookupPermutedTable p l }, ps.lookupEvals p l))))).flatten
  let fixedQ := columnQueries vk.omega x vk.fixedCommitment CommitmentId.fixedCol vk.fixedQueryLayout
    (List.ofFn ps.fixedEvals)
  let permCommonQ := permutationCommonQueries x CommitmentId.permCommon
    (List.ofFn (fun c => (vk.permutationCommonCommitment c, ps.permutationCommonEvals c)))
  let vanishingQ := vanishingQueries x hComm eHEval ps.vanishingRandom ps.vanishingRandomEval
  perProof ++ fixedQ ++ permCommonQ ++ vanishingQ

/-- The complete query list depends on instance commitments only at columns named by the VK's
instance-query layout. -/
theorem assembleQueries_congr_instanceCommitment
    {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G)
    (instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (h : ∀ p column rotation, (column, rotation) ∈ vk.instanceQueryLayout →
      instanceCommitment p column = instanceCommitment' p column) :
    assembleQueries vk instanceCommitment ps ch =
      assembleQueries vk instanceCommitment' ps ch := by
  simp only [assembleQueries]
  congr 1
  congr 1
  congr 1
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  rw [columnQueries_congr_commitment]
  exact h p

/-- If the VK's instance-query layout stays inside the configured instance-column range, agreement
on that finite range suffices for identical complete query lists. -/
theorem assembleQueries_congr_instanceCommitment_of_layout_bounded
    {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G)
    (instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (hCommitment : ∀ p column, column < shape.numInstanceColumns →
      instanceCommitment p column = instanceCommitment' p column)
    (hLayout : ∀ column rotation, (column, rotation) ∈ vk.instanceQueryLayout →
      column < shape.numInstanceColumns) :
    assembleQueries vk instanceCommitment ps ch =
      assembleQueries vk instanceCommitment' ps ch := by
  apply assembleQueries_congr_instanceCommitment vk instanceCommitment instanceCommitment' ps ch
  intro p column rotation hmem
  exact hCommitment p column (hLayout column rotation hmem)

/-- An assembled query carrying an instance-column identity uses that statement-derived commitment. -/
theorem assembleQueries_instance_commitment
    {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (q : VerifierQuery shape.k F G)
    (hq : q ∈ assembleQueries vk instanceCommitment ps ch)
    (p : Fin shape.numProofs) (column : ℕ)
    (hid : q.commId = .instanceCol p column) :
    q.commitment = .point (instanceCommitment p column) := by
  simp only [assembleQueries, List.mem_append] at hq
  rcases hq with (((hperProof | hfixed) | hcommon) | hvanishing)
  · obtain ⟨proofQueries, hproofQueries, hq⟩ := List.mem_flatten.mp hperProof
    obtain ⟨proofIndex, hproofQueries⟩ := List.mem_ofFn.mp hproofQueries
    rw [← hproofQueries] at hq
    simp only [List.mem_append] at hq
    rcases hq with hleft | hlookup
    · rcases hleft with hleft | hpermutation
      · rcases hleft with hinstance | hadvice
        · rw [columnQueries, List.mem_map] at hinstance
          obtain ⟨entry, _, hq⟩ := hinstance
          subst q
          injection hid with hproofIndex hcolumn
          have : proofIndex = p := Fin.ext hproofIndex
          subst proofIndex
          subst column
          rfl
        · rw [columnQueries, List.mem_map] at hadvice
          obtain ⟨entry, _, hq⟩ := hadvice
          subst q
          simp at hid
      · simp only [permutationQueries, List.mem_append] at hpermutation
        rcases hpermutation with hregular | hlast
        · simp only [List.mem_flatMap, List.mem_cons, List.mem_nil_iff,
            or_false] at hregular
          obtain ⟨entry, _, hq | hq⟩ := hregular
          · subst q
            simp at hid
          · subst q
            simp at hid
        · rw [List.mem_filterMap] at hlast
          obtain ⟨entry, _, hentry⟩ := hlast
          cases hlastEval : entry.1.2.lastEval with
          | none => simp [hlastEval] at hentry
          | some lastEvaluation =>
            simp [hlastEval] at hentry
            subst q
            simp at hid
    · simp only [lookupQueries, List.mem_flatMap, List.mem_cons,
        List.mem_nil_iff, or_false] at hlookup
      obtain ⟨entry, _, hq | hq | hq | hq | hq⟩ := hlookup
      all_goals
        subst q
        simp at hid
  · rw [columnQueries, List.mem_map] at hfixed
    obtain ⟨entry, _, hq⟩ := hfixed
    subst q
    simp at hid
  · rw [permutationCommonQueries, List.mem_map] at hcommon
    obtain ⟨entry, _, hq⟩ := hcommon
    subst q
    simp at hid
  · simp [vanishingQueries] at hvanishing
    rcases hvanishing with hq | hq
    · subst q
      simp at hid
    · subst q
      simp at hid

/-- An assembled query carrying a fixed-column identity uses the corresponding
verifying-key commitment. -/
theorem assembleQueries_fixed_commitment
    {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (q : VerifierQuery shape.k F G)
    (hq : q ∈ assembleQueries vk instanceCommitment ps ch)
    (column : ℕ)
    (hid : q.commId = .fixedCol column) :
    q.commitment = .point (vk.fixedCommitment column) := by
  simp only [assembleQueries, List.mem_append] at hq
  rcases hq with (((hperProof | hfixed) | hcommon) | hvanishing)
  · obtain ⟨proofQueries, hproofQueries, hq⟩ :=
      List.mem_flatten.mp hperProof
    obtain ⟨proofIndex, hproofQueries⟩ :=
      List.mem_ofFn.mp hproofQueries
    rw [← hproofQueries] at hq
    simp only [List.mem_append] at hq
    rcases hq with hleft | hlookup
    · rcases hleft with hleft | hpermutation
      · rcases hleft with hinstance | hadvice
        · rw [columnQueries, List.mem_map] at hinstance
          obtain ⟨entry, _, hq⟩ := hinstance
          subst q
          simp at hid
        · rw [columnQueries, List.mem_map] at hadvice
          obtain ⟨entry, _, hq⟩ := hadvice
          subst q
          simp at hid
      · simp only [permutationQueries, List.mem_append] at hpermutation
        rcases hpermutation with hregular | hlast
        · simp only [List.mem_flatMap, List.mem_cons, List.mem_nil_iff,
            or_false] at hregular
          obtain ⟨entry, _, hq | hq⟩ := hregular
          · subst q
            simp at hid
          · subst q
            simp at hid
        · rw [List.mem_filterMap] at hlast
          obtain ⟨entry, _, hentry⟩ := hlast
          cases hlastEval : entry.1.2.lastEval with
          | none => simp [hlastEval] at hentry
          | some lastEvaluation =>
            simp [hlastEval] at hentry
            subst q
            simp at hid
    · simp only [lookupQueries, List.mem_flatMap, List.mem_cons,
        List.mem_nil_iff, or_false] at hlookup
      obtain ⟨entry, _, hq | hq | hq | hq | hq⟩ := hlookup
      all_goals
        subst q
        simp at hid
  · rw [columnQueries, List.mem_map] at hfixed
    obtain ⟨entry, _, hq⟩ := hfixed
    subst q
    injection hid with hcolumn
    subst column
    rfl
  · rw [permutationCommonQueries, List.mem_map] at hcommon
    obtain ⟨entry, _, hq⟩ := hcommon
    subst q
    simp at hid
  · simp [vanishingQueries] at hvanishing
    rcases hvanishing with hq | hq
    · subst q
      simp at hid
    · subst q
      simp at hid

/-- An assembled query carrying a common-permutation identity uses the corresponding
verifying-key σ-column commitment. -/
theorem assembleQueries_permCommon_commitment
    {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (q : VerifierQuery shape.k F G)
    (hq : q ∈ assembleQueries vk instanceCommitment ps ch)
    (c : Fin shape.numPermutationColumns)
    (hid : q.commId = .permCommon (c : ℕ)) :
    q.commitment = .point (vk.permutationCommonCommitment c) := by
  simp only [assembleQueries, List.mem_append] at hq
  rcases hq with (((hperProof | hfixed) | hcommon) | hvanishing)
  · obtain ⟨proofQueries, hproofQueries, hq⟩ :=
      List.mem_flatten.mp hperProof
    obtain ⟨proofIndex, hproofQueries⟩ :=
      List.mem_ofFn.mp hproofQueries
    rw [← hproofQueries] at hq
    simp only [List.mem_append] at hq
    rcases hq with hleft | hlookup
    · rcases hleft with hleft | hpermutation
      · rcases hleft with hinstance | hadvice
        · rw [columnQueries, List.mem_map] at hinstance
          obtain ⟨entry, _, hq⟩ := hinstance
          subst q
          simp at hid
        · rw [columnQueries, List.mem_map] at hadvice
          obtain ⟨entry, _, hq⟩ := hadvice
          subst q
          simp at hid
      · simp only [permutationQueries, List.mem_append] at hpermutation
        rcases hpermutation with hregular | hlast
        · simp only [List.mem_flatMap, List.mem_cons, List.mem_nil_iff,
            or_false] at hregular
          obtain ⟨entry, _, hq | hq⟩ := hregular
          · subst q
            simp at hid
          · subst q
            simp at hid
        · rw [List.mem_filterMap] at hlast
          obtain ⟨entry, _, hentry⟩ := hlast
          cases hlastEval : entry.1.2.lastEval with
          | none => simp [hlastEval] at hentry
          | some lastEvaluation =>
            simp [hlastEval] at hentry
            subst q
            simp at hid
    · simp only [lookupQueries, List.mem_flatMap, List.mem_cons,
        List.mem_nil_iff, or_false] at hlookup
      obtain ⟨entry, _, hq | hq | hq | hq | hq⟩ := hlookup
      all_goals
        subst q
        simp at hid
  · rw [columnQueries, List.mem_map] at hfixed
    obtain ⟨entry, _, hq⟩ := hfixed
    subst q
    simp at hid
  · rw [permutationCommonQueries, List.mem_map] at hcommon
    obtain ⟨ce, hce, hq⟩ := hcommon
    subst q
    obtain ⟨k, hk, hcek⟩ := List.getElem_of_mem hce
    rw [List.getElem_zip] at hcek
    have hkn : k < shape.numPermutationColumns := by
      have hkzip := hk
      simp only [List.length_zip, List.length_range, List.length_ofFn,
        Nat.min_self] at hkzip
      exact hkzip
    have hce1 : ce.1 = (vk.permutationCommonCommitment ⟨k, hkn⟩,
        ps.permutationCommonEvals ⟨k, hkn⟩) := by
      rw [← hcek]
      simp
    have hce2 : ce.2 = k := by
      rw [← hcek]
      simp
    have hkc : k = (c : ℕ) := by
      simpa [hce2] using hid
    have hfin : (⟨k, hkn⟩ : Fin shape.numPermutationColumns) = c :=
      Fin.ext hkc
    simp [hce1, hfin]
  · simp [vanishingQueries] at hvanishing
    rcases hvanishing with hq | hq
    · subst q
      simp at hid
    · subst q
      simp at hid

/-- The common-permutation query list covers every index below its input length. -/
private theorem permutationCommonQueries_getElem_mem {k : ℕ} {F G : Type*} [Field F]
    (x : F) (mkId : ℕ → CommitmentId) (ces : List (G × F)) (i : ℕ)
    (hi : i < ces.length) :
    ∃ q ∈ permutationCommonQueries (k := k) x mkId ces, q.commId = mkId i := by
  have hz : i < (ces.zip (List.range ces.length)).length := by simpa using hi
  have hmem := List.mem_map_of_mem
    (f := fun ce : (G × F) × ℕ =>
      ({ point := x, commitment := .point ce.1.1, eval := ce.1.2,
         commId := mkId ce.2 } : VerifierQuery k F G))
    (List.getElem_mem hz)
  rw [permutationCommonQueries]
  refine ⟨_, hmem, ?_⟩
  simp [List.getElem_zip]

/-- Every verifying-key σ column is opened by the assembled queries: the common-permutation
queries cover the whole column family by construction. -/
theorem assembleQueries_permCommon_query
    {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (c : Fin shape.numPermutationColumns) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = .permCommon (c : ℕ) := by
  obtain ⟨q, hqmem, hqid⟩ := permutationCommonQueries_getElem_mem (k := shape.k)
    ch.x CommitmentId.permCommon
    (List.ofFn fun c => (vk.permutationCommonCommitment c, ps.permutationCommonEvals c))
    (c : ℕ) (by simp)
  refine ⟨q, ?_, hqid⟩
  simp only [assembleQueries, List.mem_append]
  exact Or.inl (Or.inr hqmem)

/-- The multiopen point-set grouping (halo2 `construct_intermediate_sets` output): per point set,
the routed queries as `(commitment, evaluations)`, the set's points, and the routed members' slot
identities, positionally aligned with `sets` (`constructIntermediateSets_sets_ids_aligned`) —
mirroring halo2's `CommitmentData`, which retains commitment identity. The identity is what ties a
decoded member back to the verifying key's query layout. Derived by `constructIntermediateSets`. -/
structure MultiopenGrouped (k : ℕ) (F G : Type*) where
  sets : List (List (CommitmentRef k F G × List F))
  ids : List (List CommitmentId)
  points : List (List F)

/-- Compress one point set by the `x₁` powers (halo2 `multiopen/verifier.rs` `accumulate`): fold the
set's query contributions, accumulating both the commitment MSM (`Σⱼ x₁ʲ cⱼ`) and the per-point
evaluation vector (`Σⱼ x₁ʲ evalsⱼ`). -/
def compressSet {k : ℕ} {F G : Type*} [Field F] (x1 : F)
    (setQueries : List (CommitmentRef k F G × List F)) (numPoints : ℕ) : Msm k F G × List F :=
  let res := setQueries.foldl (fun (st : Msm k F G × List F × F) qc =>
      (accumulateCommitment st.2.2 qc.1 st.1,
       (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
       st.2.2 * x1))
    (Msm.zero k F G, List.replicate numPoints (0 : F), (1 : F))
  (res.1, res.2.1)

/-- The multiopen opening MSM and combined value (halo2 `multiopen/verifier.rs`): compress each point
set by `x₁`, compute the combined evaluation by Lagrange interpolation at `x₃` (`multiopenEval`), then
collapse by `x₄` against `q'` (`multiopenCombine`). `u` are the prover's claimed per-set quotient
evaluations. -/
def assembleOpening {k : ℕ} {F G : Type*} [Field F] (x1 x2 x3 x4 : F) (qPrime : G) (u : List F)
    (grouped : MultiopenGrouped k F G) (incoming : Msm k F G) : Msm k F G × F :=
  let compressed := (grouped.sets.zip grouped.points).map (fun sp => compressSet x1 sp.1 sp.2.length)
  let qCommitments := compressed.map Prod.fst
  let setsForEval := ((grouped.points.zip (compressed.map Prod.snd)).zip u).map
    (fun p => (p.1.1, p.1.2, p.2))
  let msmEval := multiopenEval x2 x3 setsForEval
  multiopenCombine x4 qPrime qCommitments u msmEval incoming

/-- The final fingerprint MSM (halo2 `plonk/verifier.rs` → `multiopen/verifier.rs` →
`commitment/verifier.rs`): the multiopen opening, then the IPA fold opening it at `x₃` to the combined
value. `grouped` is the `construct_intermediate_sets` output for `assembleQueries vk instanceCommitment ps ch`. -/
def assembleFinalMsm {shape : Shape} {F G : Type*} [Field F] (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (grouped : MultiopenGrouped shape.k F G) : Msm shape.k F G :=
  let opened := assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    grouped (Msm.zero shape.k F G)
  ipaFold ch.x3 opened.2 ps.ipaC ps.ipaF ch.xi ch.z (List.ofFn ch.ipaRound) ps.ipaS
    (List.ofFn ps.ipaRounds) opened.1

/-- Evaluating the final fingerprint MSM yields the verifier's IPA verification equation. -/
theorem eval_assembleFinalMsm {shape : Shape} {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (g : Fin (2 ^ shape.k) → G) (w u : G) (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (grouped : MultiopenGrouped shape.k F G) :
    (assembleFinalMsm ps ch grouped).eval ⟨shape.k, g, w, u⟩
      = (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU) grouped
            (Msm.zero shape.k F G)).1.eval ⟨shape.k, g, w, u⟩
        + (∑ i, ([-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
            grouped (Msm.zero shape.k F G)).2].getD i.val 0) • g i)
        + ch.xi • ps.ipaS
        + (((List.ofFn ps.ipaRounds).zip (List.ofFn ch.ipaRound)).map
            (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum
        + (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) • u
        + (-ps.ipaF) • w
        + (∑ i, ((computeS (List.ofFn ch.ipaRound) (-ps.ipaC)).getD i.val 0) • g i) := by
  simp only [assembleFinalMsm]
  rw [eval_ipaFold]

/-- Re-derivation of halo2 `construct_intermediate_sets` (`poly/multiopen.rs`): group the flat
opening queries into point sets, producing the `MultiopenGrouped` that `assembleOpening` consumes
— derived in Lean rather than supplied. Queries are grouped by slot identity (`commId`, halo2's
pointer identity — see `CommitmentId`); the orderings mirror the Rust and are noted step by step
in the body. `constructIntermediateSets?` is the rejecting form. -/
def constructIntermediateSets {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G)) : MultiopenGrouped k F G :=
  -- distinct points, in first-appearance order; `pointIdx p` is `p`'s index in that order
  let points : List F :=
    queries.foldl (fun acc q => if q.point ∈ acc then acc else acc ++ [q.point]) []
  let pointIdx : F → ℕ := fun p => points.findIdx (fun x => decide (x = p))
  -- distinct commitments by slot identity (`commId`), in first-appearance order (halo2 `IndexMap` by
  -- pointer identity); the paired `CommitmentRef` is the curve value the group contributes to the MSM
  let comms : List (CommitmentId × CommitmentRef k F G) :=
    queries.foldl (fun acc q => if acc.any (fun c => decide (c.1 = q.commId)) then acc
      else acc ++ [(q.commId, q.commitment)]) []
  -- per commitment (halo2 `CommitmentData`, identity retained): its slot identity, curve value,
  -- ascending point-index set, and eval vector over that set
  let commData : List (CommitmentId × CommitmentRef k F G × List ℕ × List F) :=
    comms.map fun c =>
      let qs := queries.filter fun q => decide (q.commId = c.1)
      let idxs := qs.map fun q => pointIdx q.point
      let idxSet := (List.range points.length).filter fun i => idxs.contains i
      let evals := idxSet.filterMap fun i =>
        (qs.find? fun q => decide (pointIdx q.point = i)).map (·.eval)
      (c.1, c.2, idxSet, evals)
  -- distinct point-index sets, first-appearance order (over commitments) → set index
  let setList : List (List ℕ) :=
    commData.foldl (fun acc cd => if cd.2.2.1 ∈ acc then acc else acc ++ [cd.2.2.1]) []
  let setIdx : List ℕ → ℕ := fun s => setList.findIdx fun x => decide (x = s)
  -- accumulate order is reversed commitment order; per set, the members routed to it — `sets`
  -- (curve value, evals) and `ids` (slot identity) are projections of the same routed list, so
  -- they are positionally aligned by construction
  let revData := commData.reverse
  let routed : ℕ → List (CommitmentId × CommitmentRef k F G × List ℕ × List F) :=
    fun si => revData.filter fun cd => decide (setIdx cd.2.2.1 = si)
  let sets : List (List (CommitmentRef k F G × List F)) :=
    (List.range setList.length).map fun si => (routed si).map fun cd => (cd.2.1, cd.2.2.2)
  let ids : List (List CommitmentId) :=
    (List.range setList.length).map fun si => (routed si).map (·.1)
  -- per set, its points in ascending point-index order
  let setPoints : List (List F) := setList.map fun s => s.filterMap fun i => points[i]?
  { sets := sets, ids := ids, points := setPoints }

/-- Grouped `ids` and `sets` are aligned projections with equal per-set lengths. -/
theorem constructIntermediateSets_sets_ids_aligned {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) (i : ℕ) :
    ((constructIntermediateSets queries).ids.getD i []).length
      = ((constructIntermediateSets queries).sets.getD i []).length := by
  simp only [constructIntermediateSets, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases h : (List.range _)[i]? with _ | si
  · simp
  · simp [List.length_map]

/-- The `ids` view has one entry per point set, aligned with `sets`. -/
theorem constructIntermediateSets_ids_length {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) :
    (constructIntermediateSets queries).ids.length
      = (constructIntermediateSets queries).sets.length := by
  simp [constructIntermediateSets]

/-- `sets` and `points` have one entry per point set. -/
theorem constructIntermediateSets_points_length {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) :
    (constructIntermediateSets queries).sets.length
      = (constructIntermediateSets queries).points.length := by
  simp [constructIntermediateSets]

/-- Projecting the first component of the `sets.zip points` view (`deployedSetQueries`'s shape) is
the plain `sets` entry — the zip never truncates, since `sets` and `points` are equal-length. -/
theorem constructIntermediateSets_zip_sets_getD {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) (i : ℕ) :
    (((constructIntermediateSets queries).sets.zip
        (constructIntermediateSets queries).points).getD i ([], [])).1
      = (constructIntermediateSets queries).sets.getD i [] := by
  have hlen := constructIntermediateSets_points_length queries
  rcases lt_or_ge i (constructIntermediateSets queries).sets.length with hi | hi
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_zip, ← hlen, min_self]; exact hi),
      List.getElem_zip, List.getD_eq_getElem _ _ hi]
  · rw [List.getD_eq_default _ _ (by rw [List.length_zip, ← hlen, min_self]; exact hi),
      List.getD_eq_default _ _ hi]

/-- Anything already in the accumulator survives the first-appearance dedup fold. -/
theorem mem_dedup_foldl_mono {α β : Type*} [DecidableEq β] (l : List α) (f : α → β) :
    ∀ (init : List β) (x : β), x ∈ init →
      x ∈ l.foldl (fun acc a => if f a ∈ acc then acc else acc ++ [f a]) init := by
  induction l with
  | nil => intro init x hx; simpa using hx
  | cons a l ih =>
      intro init x hx
      rw [List.foldl_cons]
      apply ih
      by_cases h : f a ∈ init
      · rwa [if_pos h]
      · rw [if_neg h]; exact List.mem_append.mpr (Or.inl hx)

/-- Every element's image under `f` lands in the first-appearance dedup fold over `l`. -/
theorem mem_dedup_foldl {α β : Type*} [DecidableEq β] (l : List α) (f : α → β) :
    ∀ (init : List β) {a : α}, a ∈ l →
      f a ∈ l.foldl (fun acc b => if f b ∈ acc then acc else acc ++ [f b]) init := by
  induction l with
  | nil => intro init a ha; exact absurd ha (List.not_mem_nil)
  | cons c l ih =>
      intro init a ha
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | ha'
      · apply mem_dedup_foldl_mono
        by_cases h : f a ∈ init
        · rwa [if_pos h]
        · rw [if_neg h]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      · exact ih _ ha'

/-- `findIdx` of a present element retrieves it: the option-get at that index is the element. -/
theorem getElem?_findIdx_self {α : Type*} [DecidableEq α] {l : List α} {x : α}
    (h : x ∈ l) : l[l.findIdx (fun y => decide (y = x))]? = some x := by
  have hex : ∃ z ∈ l, (fun y => decide (y = x)) z = true := ⟨x, h, by simp⟩
  have hlt : l.findIdx (fun y => decide (y = x)) < l.length :=
    List.findIdx_lt_length_of_exists hex
  rw [List.getElem?_eq_getElem hlt]
  have hval := List.findIdx_getElem (p := fun y => decide (y = x)) (xs := l) (w := hlt)
  simp only [decide_eq_true_eq] at hval
  rw [hval]

/-- A routed query's opening point occurs in its grouped point set. -/
theorem constructIntermediateSets_point_mem {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G))
    {q : VerifierQuery k F G} (hq : q ∈ queries) {si m : ℕ} {d₀ : CommitmentId}
    (hlt : m < ((constructIntermediateSets queries).ids.getD si []).length)
    (hid : ((constructIntermediateSets queries).ids.getD si []).getD m d₀ = q.commId) :
    q.point ∈ (constructIntermediateSets queries).points.getD si [] := by
  classical
  -- positional `getD` → membership: `q.commId` is a member of set `si`'s id list
  have hmem : q.commId ∈ (constructIntermediateSets queries).ids.getD si [] := by
    have h1 : ((constructIntermediateSets queries).ids.getD si [])[m] = q.commId := by
      rw [← hid, List.getD_eq_getElem _ _ hlt]
    exact h1 ▸ List.getElem_mem hlt
  simp only [constructIntermediateSets] at hmem ⊢
  -- reduce `ids.getD si` (a `(range _).map _` list) to its `si`-th entry
  rw [List.getD_eq_getElem?_getD, List.getElem?_map] at hmem
  rcases hrange : (List.range _)[si]? with _ | j
  · rw [hrange] at hmem
    simp only [Option.map_none, Option.getD_none, List.not_mem_nil] at hmem
  · rw [hrange] at hmem
    obtain ⟨hsiN, hjval⟩ := List.getElem?_eq_some_iff.mp hrange
    rw [List.getElem_range] at hjval
    subst j
    simp only [Option.map_some, Option.getD_some] at hmem
    obtain ⟨cd, hcd, hcd1⟩ := List.mem_map.mp hmem
    -- `cd` is routed to `si` and its commId is `q.commId`
    rw [List.mem_filter] at hcd
    obtain ⟨hcdrev, hcddec⟩ := hcd
    rw [decide_eq_true_eq] at hcddec
    rw [List.mem_reverse] at hcdrev
    -- `cd`'s point-index set is set `si`'s distinct index list, so `points.getD si` filters it
    have hcdset := mem_dedup_foldl _ (fun x => x.2.2.1) ([] : List (List ℕ)) hcdrev
    have hsi := getElem?_findIdx_self hcdset
    simp only [hcddec] at hsi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hsi, Option.map_some,
      Option.getD_some, List.mem_filterMap]
    -- the point-index of `q.point` witnesses membership: it is a valid index retrieving `q.point`,
    -- and it lies in `cd`'s (hence set `si`'s) index set because `q` is one of `cd`'s queries
    refine ⟨(List.foldl (fun acc q => if q.point ∈ acc then acc else acc ++ [q.point]) []
      queries).findIdx (fun y => decide (y = q.point)), ?_, ?_⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcdrev
      refine List.mem_filter.mpr ⟨?_, ?_⟩
      · rw [List.mem_range]
        exact List.findIdx_lt_length_of_exists
          ⟨q.point, mem_dedup_foldl _ (fun x => x.point) [] hq, by simp⟩
      · exact (List.contains_iff_mem).mpr (List.mem_map.mpr
          ⟨q, List.mem_filter.mpr ⟨hq, by rw [decide_eq_true_eq]; exact hcd1.symm⟩, rfl⟩)
    · exact getElem?_findIdx_self (mem_dedup_foldl _ (fun x => x.point) [] hq)

/-- The first-appearance dedup fold produces a `Nodup` list (it appends only elements not already
present). -/
theorem nodup_dedup_foldl {α β : Type*} [DecidableEq β] (l : List α) (f : α → β) :
    ∀ (init : List β), init.Nodup →
      (l.foldl (fun acc a => if f a ∈ acc then acc else acc ++ [f a]) init).Nodup := by
  induction l with
  | nil => intro init h; simpa using h
  | cons a l ih =>
      intro init h
      rw [List.foldl_cons]
      apply ih
      by_cases hmem : f a ∈ init
      · rwa [if_pos hmem]
      · rw [if_neg hmem]
        exact List.Nodup.append h (List.nodup_singleton _) (List.disjoint_singleton.mpr hmem)

/-- Each grouped point set contains no duplicate points. -/
theorem constructIntermediateSets_points_nodup {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G)) (idx : ℕ) :
    ((constructIntermediateSets queries).points.getD idx []).Nodup := by
  classical
  have key : ∀ ps ∈ (constructIntermediateSets queries).points, ps.Nodup := by
    intro ps hps
    simp only [constructIntermediateSets] at hps
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hps
    -- `s` is one of the distinct point-index sets, hence a filtered `range`, hence `Nodup`
    -- (via a fold invariant on the actual `setList` fold, to match its membership instance)
    have hsnodup : s.Nodup := by
      refine List.foldlRecOn (motive := fun acc : List (List ℕ) => ∀ x ∈ acc, x.Nodup)
        _ _ ?_ ?_ s hs
      · intro x hx; exact absurd hx (List.not_mem_nil)
      · intro acc hacc cd hcd
        split
        · exact hacc
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hacc x h
          · rw [List.mem_singleton] at h
            subst h
            obtain ⟨c, -, rfl⟩ := List.mem_map.mp hcd
            exact List.Nodup.filter _ List.nodup_range
    -- the internal points list is `Nodup`
    have hpnodup : (queries.foldl (fun acc q => if q.point ∈ acc then acc else acc ++ [q.point])
        ([] : List F)).Nodup := nodup_dedup_foldl queries (·.point) [] List.nodup_nil
    -- `filterMap (points[·]?)` preserves `Nodup`: distinct valid indices give distinct entries
    refine List.Nodup.filterMap ?_ hsnodup
    intro i i' b hb hb'
    rw [Option.mem_def, List.getElem?_eq_some_iff] at hb hb'
    obtain ⟨hi, hbi⟩ := hb
    obtain ⟨hi', hbi'⟩ := hb'
    have h2 : (⟨i, hi⟩ : Fin _) = ⟨i', hi'⟩ :=
      List.nodup_iff_injective_getElem.mp hpnodup (hbi.trans hbi'.symm)
    exact congrArg Fin.val h2
  rcases lt_or_ge idx (constructIntermediateSets queries).points.length with hlt | hge
  · rw [List.getD_eq_getElem _ _ hlt]; exact key _ (List.getElem_mem hlt)
  · rw [List.getD_eq_default _ _ hge]; exact List.nodup_nil

/-- Two `filterMap`s over the same list have equal length when both functions are everywhere
defined on it. -/
private theorem length_filterMap_eq_of_forall_isSome {α β γ : Type*}
    {f : α → Option β} {g : α → Option γ} :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome) → (∀ x ∈ l, (g x).isSome) →
      (l.filterMap f).length = (l.filterMap g).length := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a l ih =>
      intro hf hg
      have hfa := hf a (List.mem_cons_self ..)
      have hga := hg a (List.mem_cons_self ..)
      rw [List.filterMap_cons, List.filterMap_cons]
      rcases ha : f a with _ | b
      · rw [ha] at hfa; exact absurd hfa (by simp)
      rcases hb : g a with _ | c
      · rw [hb] at hga; exact absurd hga (by simp)
      simp only [List.length_cons]
      exact congrArg Nat.succ (ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
        (fun x hx => hg x (List.mem_cons_of_mem _ hx)))

/-- Each grouped member supplies one evaluation per point in its set. -/
theorem constructIntermediateSets_eval_length {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G)) (i : ℕ) :
    ∀ qc ∈ (constructIntermediateSets queries).sets.getD i [],
      qc.2.length = ((constructIntermediateSets queries).points.getD i []).length := by
  classical
  intro qc hqc
  simp only [constructIntermediateSets] at hqc ⊢
  rw [List.getD_eq_getElem?_getD, List.getElem?_map] at hqc
  rcases hrange : (List.range _)[i]? with _ | j
  · rw [hrange] at hqc
    simp only [Option.map_none, Option.getD_none, List.not_mem_nil] at hqc
  · rw [hrange] at hqc
    obtain ⟨hsiN, hjval⟩ := List.getElem?_eq_some_iff.mp hrange
    rw [List.getElem_range] at hjval
    subst j
    simp only [Option.map_some, Option.getD_some] at hqc
    obtain ⟨cd, hcd, rfl⟩ := List.mem_map.mp hqc
    -- `cd` is routed to set `i`: its point-index set is `setList[i]`
    rw [List.mem_filter] at hcd
    obtain ⟨hcdrev, hcddec⟩ := hcd
    rw [decide_eq_true_eq] at hcddec
    rw [List.mem_reverse] at hcdrev
    have hcdset := mem_dedup_foldl _ (fun x => x.2.2.1) ([] : List (List ℕ)) hcdrev
    have hsi := getElem?_findIdx_self hcdset
    simp only [hcddec] at hsi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hsi, Option.map_some,
      Option.getD_some]
    -- `cd` comes from `commData`: its evals are a `filterMap` over its own index set
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcdrev
    -- both `filterMap`s are everywhere defined on the index set
    refine length_filterMap_eq_of_forall_isSome _ ?_ ?_
    · intro x hx
      rw [List.mem_filter] at hx
      have hxq := (List.contains_iff_mem).mp hx.2
      obtain ⟨q, hq, hqi⟩ := List.mem_map.mp hxq
      have hfind : (List.find? (fun q' => decide ((List.foldl
          (fun acc q'' => if q''.point ∈ acc then acc else acc ++ [q''.point]) [] queries).findIdx
            (fun y => decide (y = q'.point)) = x))
          (queries.filter (fun q' => decide (q'.commId = c.1)))).isSome := by
        rw [List.find?_isSome]
        exact ⟨q, hq, by simp [hqi]⟩
      simpa using hfind
    · intro x hx
      rw [List.mem_filter, List.mem_range] at hx
      rw [List.getElem?_eq_getElem hx.1]
      exact Option.isSome_some

/-! ### Unique-slot routing (the vanishing-slot eval faithfulness)

The vanishing-`h` query carries a *verifier-computed* claimed evaluation and is the only query on
its slot. The lemmas below track such a unique-slot query through the grouping pipeline: the
`cis*` definitions name `constructIntermediateSets`' internal stages (each definitionally
equal to the corresponding `let`), the fold helpers characterize the keyed commitment dedup, and
`constructIntermediateSets_unique_comm_routed` concludes the query is routed to a member whose
recorded evaluation list is exactly `[q.eval]`, in a point set whose point list is exactly
`[q.point]`. `assembleQueries_vanishingH_unique` supplies the uniqueness for the vanishing slot,
and `Soundness.Multiopen.ValueCheckDeployed.deployed_vanishingH_routed` reads the result off in
the deployed `getD` shapes — the grouping-side fact the `hfold` derivation consumes. -/

/-- The grouping's internal distinct-points list (first-appearance order). -/
def cisPts {k : ℕ} {F G : Type*} (queries : List (VerifierQuery k F G))
    [DecidableEq F] : List F :=
  queries.foldl (fun acc q => if q.point ∈ acc then acc else acc ++ [q.point]) []

/-- The grouping's internal point index. -/
def cisPIdx {k : ℕ} {F G : Type*} (queries : List (VerifierQuery k F G))
    [DecidableEq F] (p : F) : ℕ :=
  (cisPts queries).findIdx fun x => decide (x = p)

/-- The grouping's internal keyed distinct-commitments list. -/
def cisComms {k : ℕ} {F G : Type*} (queries : List (VerifierQuery k F G)) :
    List (CommitmentId × CommitmentRef k F G) :=
  queries.foldl (fun acc q => if acc.any (fun c => decide (c.1 = q.commId)) then acc
    else acc ++ [(q.commId, q.commitment)]) []

/-- The grouping's internal per-commitment data: identity, curve value, ascending point-index
set, and eval vector over that set. -/
def cisData {k : ℕ} {F G : Type*} (queries : List (VerifierQuery k F G))
    [DecidableEq F] : List (CommitmentId × CommitmentRef k F G × List ℕ × List F) :=
  (cisComms queries).map fun c =>
    let qs := queries.filter fun q => decide (q.commId = c.1)
    let idxs := qs.map fun q => cisPIdx queries q.point
    let idxSet := (List.range (cisPts queries).length).filter fun i => idxs.contains i
    let evals := idxSet.filterMap fun i =>
      (qs.find? fun q => decide (cisPIdx queries q.point = i)).map (·.eval)
    (c.1, c.2, idxSet, evals)

/-- The grouping's internal distinct point-index sets (first-appearance order over commitments). -/
def cisSetList {k : ℕ} {F G : Type*} (queries : List (VerifierQuery k F G))
    [DecidableEq F] : List (List ℕ) :=
  (cisData queries).foldl (fun acc cd => if cd.2.2.1 ∈ acc then acc else acc ++ [cd.2.2.1]) []

/-- The members routed to point set `si`, in accumulate order. -/
def cisRouted {k : ℕ} {F G : Type*} (queries : List (VerifierQuery k F G))
    [DecidableEq F] (si : ℕ) :
    List (CommitmentId × CommitmentRef k F G × List ℕ × List F) :=
  (cisData queries).reverse.filter fun cd =>
    decide ((cisSetList queries).findIdx (fun x => decide (x = cd.2.2.1)) = si)

/-- Anything already in the keyed accumulator survives the keyed dedup fold. -/
theorem cisComms_fold_mono {k : ℕ} {F G : Type*} (l : List (VerifierQuery k F G)) :
    ∀ (init : List (CommitmentId × CommitmentRef k F G))
      {e : CommitmentId × CommitmentRef k F G}, e ∈ init →
      e ∈ l.foldl (fun acc q => if acc.any (fun c => decide (c.1 = q.commId)) then acc
        else acc ++ [(q.commId, q.commitment)]) init := by
  induction l with
  | nil => intro init e he; simpa using he
  | cons a l ih =>
      intro init e he
      rw [List.foldl_cons]
      by_cases h : init.any (fun c => decide (c.1 = a.commId)) = true
      · rw [if_pos h]; exact ih init he
      · rw [if_neg h]; exact ih _ (List.mem_append.mpr (Or.inl he))

/-- Every query's slot identity is keyed by the keyed dedup fold. -/
theorem cisComms_fold_covers {k : ℕ} {F G : Type*} (l : List (VerifierQuery k F G)) :
    ∀ (init : List (CommitmentId × CommitmentRef k F G)) {q : VerifierQuery k F G}, q ∈ l →
      ∃ e ∈ l.foldl (fun acc q' => if acc.any (fun c => decide (c.1 = q'.commId)) then acc
        else acc ++ [(q'.commId, q'.commitment)]) init, e.1 = q.commId := by
  induction l with
  | nil => intro _ _ hq; exact absurd hq List.not_mem_nil
  | cons a l ih =>
      intro init q hq
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hq with rfl | hq'
      · by_cases h : init.any (fun c => decide (c.1 = q.commId)) = true
        · rw [if_pos h]
          obtain ⟨e, he, hek⟩ := List.any_eq_true.mp h
          exact ⟨e, cisComms_fold_mono l init he, by simpa using hek⟩
        · rw [if_neg h]
          refine ⟨(q.commId, q.commitment), cisComms_fold_mono l _ ?_, rfl⟩
          exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      · by_cases h : init.any (fun c => decide (c.1 = a.commId)) = true
        · rw [if_pos h]; exact ih init hq'
        · rw [if_neg h]; exact ih _ hq'

/-- The keyed dedup fold grows by at most one entry per query. -/
theorem cisComms_fold_length_le {k : ℕ} {F G : Type*}
    (l : List (VerifierQuery k F G)) :
    ∀ init : List (CommitmentId × CommitmentRef k F G),
      (l.foldl (fun acc q => if acc.any (fun c => decide (c.1 = q.commId)) then acc
        else acc ++ [(q.commId, q.commitment)]) init).length ≤ init.length + l.length := by
  induction l with
  | nil => intro init; simp
  | cons a t ih =>
      intro init
      rw [List.foldl_cons]
      by_cases h : init.any (fun c => decide (c.1 = a.commId)) = true
      · rw [if_pos h]
        exact le_trans (ih init) (by rw [List.length_cons]; omega)
      · rw [if_neg h]
        refine le_trans (ih _) ?_
        rw [List.length_append, List.length_singleton, List.length_cons]
        omega

/-- Each point set routes at most one member per query. -/
theorem constructIntermediateSets_sets_getD_length_le {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) (i : ℕ) :
    ((constructIntermediateSets queries).sets.getD i []).length ≤ queries.length := by
  classical
  have hcomms : (cisComms queries).length ≤ queries.length := by
    have h := cisComms_fold_length_le queries []
    rw [List.length_nil, Nat.zero_add] at h
    rw [cisComms]
    exact h
  have hdata : (cisData queries).length = (cisComms queries).length := by
    rw [cisData, List.length_map]
  have hrouted : ∀ si, (cisRouted queries si).length ≤ (cisData queries).length := by
    intro si
    rw [cisRouted]
    exact le_trans (List.length_filter_le _ _) (by rw [List.length_reverse])
  show (((List.range (cisSetList queries).length).map fun si =>
    (cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2)).getD i []).length ≤ queries.length
  rcases lt_or_ge i ((List.range (cisSetList queries).length).map fun si =>
      (cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2)).length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi, List.getElem_map, List.length_map]
    exact le_trans (hrouted _) (hdata ▸ hcomms)
  · rw [List.getD_eq_default _ _ hi]
    exact Nat.zero_le _

/-- Every entry of the keyed dedup fold is an initial entry or the key–value pair of some list
element. -/
theorem cisComms_fold_prov {k : ℕ} {F G : Type*} (l : List (VerifierQuery k F G)) :
    ∀ (init : List (CommitmentId × CommitmentRef k F G))
      {e : CommitmentId × CommitmentRef k F G},
      e ∈ l.foldl (fun acc q => if acc.any (fun c => decide (c.1 = q.commId)) then acc
        else acc ++ [(q.commId, q.commitment)]) init →
      e ∈ init ∨ ∃ q ∈ l, e = (q.commId, q.commitment) := by
  induction l with
  | nil => intro init e he; exact Or.inl (by simpa using he)
  | cons a l ih =>
      intro init e he
      rw [List.foldl_cons] at he
      by_cases h : init.any (fun c => decide (c.1 = a.commId)) = true
      · rw [if_pos h] at he
        rcases ih init he with h1 | ⟨b, hb, rfl⟩
        · exact Or.inl h1
        · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, rfl⟩
      · rw [if_neg h] at he
        rcases ih _ he with h1 | ⟨b, hb, rfl⟩
        · rcases List.mem_append.mp h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr ⟨a, List.mem_cons_self .., List.mem_singleton.mp h2⟩
        · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, rfl⟩

/-- Filtering `range n` by equality with `j < n` leaves exactly `[j]`. -/
theorem range_filter_eq_singleton {j n : ℕ} (h : j < n) :
    (List.range n).filter (fun i => decide (i = j)) = [j] := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ, List.filter_append]
      rcases Nat.lt_or_ge j n with hj | hj
      · rw [ih hj]
        have h2 : List.filter (fun i => decide (i = j)) [n] = [] := by
          have hne : ¬ (n = j) := by omega
          simp [hne]
        rw [h2, List.append_nil]
      · have hjn : j = n := by omega
        subst hjn
        have h1 : (List.range j).filter (fun i => decide (i = j)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro a ha
          simp only [decide_eq_true_eq]
          exact Nat.ne_of_lt (List.mem_range.mp ha)
        rw [h1, List.nil_append]
        simp

/-- A unique-slot query's per-commitment data entry: its own identity and curve value, the
singleton index set of its point, and the singleton eval list of its claimed evaluation. -/
theorem cisData_unique_entry {k : ℕ} {F G : Type*} [DecidableEq F]
    (queries : List (VerifierQuery k F G)) {q : VerifierQuery k F G} (hq : q ∈ queries)
    (huniq : ∀ q' ∈ queries, q'.commId = q.commId → q' = q) :
    (q.commId, q.commitment, [cisPIdx queries q.point], [q.eval]) ∈ cisData queries := by
  classical
  have hcomm : (q.commId, q.commitment) ∈ cisComms queries := by
    obtain ⟨e, he, hek⟩ := cisComms_fold_covers queries [] hq
    rcases cisComms_fold_prov queries [] he with h0 | ⟨q', hq', rfl⟩
    · exact absurd h0 List.not_mem_nil
    · have hqq : q' = q := huniq q' hq' hek
      subst hqq; exact he
  have hqsall : ∀ q' ∈ queries.filter (fun q'' => decide (q''.commId = q.commId)), q' = q := by
    intro q' hq'
    have h1 := List.mem_filter.mp hq'
    exact huniq q' h1.1 (by simpa using h1.2)
  have hqmem : q ∈ queries.filter (fun q'' => decide (q''.commId = q.commId)) :=
    List.mem_filter.mpr ⟨hq, by simp⟩
  have hlt : cisPIdx queries q.point < (cisPts queries).length :=
    List.findIdx_lt_length_of_exists
      ⟨q.point, mem_dedup_foldl queries (·.point) [] hq, by simp⟩
  -- the index set is the singleton of the query's point index
  have hidxset : (List.range (cisPts queries).length).filter
      (fun i => ((queries.filter (fun q'' => decide (q''.commId = q.commId))).map
        (fun q' => cisPIdx queries q'.point)).contains i) = [cisPIdx queries q.point] := by
    rw [← range_filter_eq_singleton hlt]
    refine List.filter_congr ?_
    intro i _
    rw [Bool.eq_iff_iff]
    simp only [List.contains_iff_mem, decide_eq_true_eq]
    constructor
    · intro hmem
      obtain ⟨q', hq', hq'i⟩ := List.mem_map.mp hmem
      rw [hqsall q' hq'] at hq'i
      exact hq'i.symm
    · intro hi
      subst hi
      exact List.mem_map.mpr ⟨q, hqmem, rfl⟩
  -- the eval list is the singleton of the query's claimed evaluation
  have hfind : ((queries.filter (fun q'' => decide (q''.commId = q.commId))).find?
      (fun q' => decide (cisPIdx queries q'.point = cisPIdx queries q.point))) = some q := by
    rcases hcons : queries.filter (fun q'' => decide (q''.commId = q.commId)) with _ | ⟨h₀, t⟩
    · rw [hcons] at hqmem; exact absurd hqmem List.not_mem_nil
    · have hh : h₀ = q := hqsall h₀ (by rw [hcons]; exact List.mem_cons_self ..)
      subst hh
      rw [hcons]
      refine List.find?_cons_of_pos ?_
      simp only [decide_eq_true_eq]
  refine List.mem_map.mpr ⟨(q.commId, q.commitment), hcomm, ?_⟩
  show (q.commId, q.commitment,
      (List.range (cisPts queries).length).filter
        (fun i => ((queries.filter (fun q'' => decide (q''.commId = q.commId))).map
          (fun q' => cisPIdx queries q'.point)).contains i),
      ((List.range (cisPts queries).length).filter
        (fun i => ((queries.filter (fun q'' => decide (q''.commId = q.commId))).map
          (fun q' => cisPIdx queries q'.point)).contains i)).filterMap
        (fun i => ((queries.filter (fun q'' => decide (q''.commId = q.commId))).find?
          (fun q' => decide (cisPIdx queries q'.point = i))).map (·.eval)))
    = (q.commId, q.commitment, [cisPIdx queries q.point], [q.eval])
  rw [hidxset]
  have hfm : ([cisPIdx queries q.point].filterMap
      (fun i => ((queries.filter (fun q'' => decide (q''.commId = q.commId))).find?
        (fun q' => decide (cisPIdx queries q'.point = i))).map (·.eval))) = [q.eval] := by
    rw [List.filterMap_cons, hfind]; rfl
  rw [hfm]

/-- A uniquely identified query is routed with its point and claimed evaluation. -/
theorem constructIntermediateSets_unique_comm_routed {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) {q : VerifierQuery k F G}
    (hq : q ∈ queries) (huniq : ∀ q' ∈ queries, q'.commId = q.commId → q' = q) :
    ∃ i, i < (constructIntermediateSets queries).sets.length ∧
      (constructIntermediateSets queries).points.getD i [] = [q.point] ∧
      ∃ m, m < ((constructIntermediateSets queries).sets.getD i []).length ∧
        (∀ c₀, ((constructIntermediateSets queries).ids.getD i []).getD m c₀ = q.commId) ∧
        ∀ d₀, ((constructIntermediateSets queries).sets.getD i []).getD m d₀
          = (q.commitment, [q.eval]) := by
  classical
  have hcd := cisData_unique_entry queries hq huniq
  have hslmem : [cisPIdx queries q.point] ∈ cisSetList queries := by
    have h1 := mem_dedup_foldl (cisData queries) (fun x => x.2.2.1) [] hcd
    simpa using h1
  have hsilt : (cisSetList queries).findIdx
      (fun x => decide (x = [cisPIdx queries q.point])) < (cisSetList queries).length :=
    List.findIdx_lt_length_of_exists ⟨[cisPIdx queries q.point], hslmem, by simp⟩
  have hsiget : (cisSetList queries)[(cisSetList queries).findIdx
      (fun x => decide (x = [cisPIdx queries q.point]))]? = some [cisPIdx queries q.point] :=
    getElem?_findIdx_self hslmem
  set si := (cisSetList queries).findIdx (fun x => decide (x = [cisPIdx queries q.point]))
    with hsi
  have hrouted : (q.commId, q.commitment, [cisPIdx queries q.point], [q.eval])
      ∈ cisRouted queries si := by
    rw [cisRouted]
    refine List.mem_filter.mpr ⟨List.mem_reverse.mpr hcd, ?_⟩
    simp [hsi]
  obtain ⟨m, hm, hrm⟩ := List.mem_iff_getElem.mp hrouted
  refine ⟨si, ?_, ?_, m, ?_, ?_, ?_⟩
  · show si < ((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).length
    rw [List.length_map, List.length_range]
    exact hsilt
  · show ((cisSetList queries).map fun s => s.filterMap fun i => (cisPts queries)[i]?).getD si []
      = [q.point]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hsiget]
    have hjget : (cisPts queries)[cisPIdx queries q.point]? = some q.point := by
      simp only [cisPIdx]
      exact getElem?_findIdx_self (mem_dedup_foldl queries (·.point) [] hq)
    simp [hjget]
  · show m < (((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).getD si []).length
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [List.length_range]; exact hsilt), List.getElem_range]
    simpa using hm
  · intro c₀
    show (((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map (·.1)).getD si []).getD m c₀ = q.commId
    have hlen1 : si < ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map (·.1)).length := by
      rw [List.length_map, List.length_range]; exact hsilt
    have hin : ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map (·.1)).getD si [] = (cisRouted queries si).map (·.1) := by
      rw [List.getD_eq_getElem _ _ hlen1, List.getElem_map, List.getElem_range]
    rw [hin, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm), List.getElem_map, hrm]
  · intro d₀
    show (((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).getD si []).getD m d₀
      = (q.commitment, [q.eval])
    have hlen1 : si < ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).length := by
      rw [List.length_map, List.length_range]; exact hsilt
    have hin : ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).getD si []
        = (cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2) := by
      rw [List.getD_eq_getElem _ _ hlen1, List.getElem_map, List.getElem_range]
    rw [hin, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm), List.getElem_map, hrm]

/-! ### Vanishing-slot uniqueness

Every builder tags its queries with its own `CommitmentId` constructor family; only
`vanishingQueries` emits the `vanishingH` slot, and it does so exactly once. So the vanishing-`h`
query is the unique carrier of its slot in `assembleQueries` — the uniqueness
`constructIntermediateSets_unique_comm_routed` needs to route it unambiguously. -/

/-- Every column query uses an identifier produced by `mkId`. -/
theorem columnQueries_commId_form {k : ℕ} {F G : Type*} [Field F] {omega x : F}
    {comm : ℕ → G} {mkId : ℕ → CommitmentId} {layout : List (ℕ × ℤ)} {evals : List F}
    {q : VerifierQuery k F G} (hq : q ∈ columnQueries omega x comm mkId layout evals) :
    ∃ n, q.commId = mkId n := by
  rw [columnQueries, List.mem_map] at hq
  obtain ⟨e, _, rfl⟩ := hq
  exact ⟨e.1.1, rfl⟩

/-- Every common-permutation query uses an identifier produced by `mkId`. -/
theorem permutationCommonQueries_commId_form {k : ℕ} {F G : Type*} [Field F] {x : F}
    {mkId : ℕ → CommitmentId} {commsEvals : List (G × F)} {q : VerifierQuery k F G}
    (hq : q ∈ permutationCommonQueries x mkId commsEvals) : ∃ n, q.commId = mkId n := by
  rw [permutationCommonQueries, List.mem_map] at hq
  obtain ⟨e, _, rfl⟩ := hq
  exact ⟨e.2, rfl⟩

/-- Every permutation query uses an identifier produced by `mkId`. -/
theorem permutationQueries_commId_form {k : ℕ} {F G : Type*} [Field F]
    {x xNext xLast : F} {mkId : ℕ → CommitmentId} {sets : List (G × PermSetEval F)}
    {q : VerifierQuery k F G} (hq : q ∈ permutationQueries x xNext xLast mkId sets) :
    ∃ n, q.commId = mkId n := by
  rw [permutationQueries, List.mem_append] at hq
  rcases hq with hq | hq
  · rw [List.mem_flatMap] at hq
    obtain ⟨s, _, hq⟩ := hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact ⟨s.2, rfl⟩
  · rw [List.mem_filterMap] at hq
    obtain ⟨s, _, hq⟩ := hq
    obtain ⟨le, _, rfl⟩ := by simpa using hq
    exact ⟨s.2, rfl⟩

/-- Every lookup query uses a product, input, or table identifier. -/
theorem lookupQueries_commId_form {k : ℕ} {F G : Type*} [Field F] {x xInv xNext : F}
    {mkProduct mkInput mkTable : ℕ → CommitmentId}
    {lookups : List (LookupCommitments G × LookupEval F)} {q : VerifierQuery k F G}
    (hq : q ∈ lookupQueries x xInv xNext mkProduct mkInput mkTable lookups) :
    ∃ n, q.commId = mkProduct n ∨ q.commId = mkInput n ∨ q.commId = mkTable n := by
  rw [lookupQueries, List.mem_flatMap] at hq
  obtain ⟨l, _, hq⟩ := hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨l.2, Or.inl rfl⟩
  · exact ⟨l.2, Or.inr (Or.inl rfl)⟩
  · exact ⟨l.2, Or.inr (Or.inr rfl)⟩
  · exact ⟨l.2, Or.inr (Or.inl rfl)⟩
  · exact ⟨l.2, Or.inl rfl⟩

/-- **Vanishing-slot uniqueness.** Any two queries of `assembleQueries` on the `vanishingH` slot are
equal — the vanishing-`h` query is the sole carrier of its slot. -/
theorem assembleQueries_vanishingH_unique {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    {q₁ q₂ : VerifierQuery shape.k F G}
    (hq₁ : q₁ ∈ assembleQueries vk instanceCommitment ps ch)
    (hq₂ : q₂ ∈ assembleQueries vk instanceCommitment ps ch)
    (hv₁ : q₁.commId = CommitmentId.vanishingH) (hv₂ : q₂.commId = CommitmentId.vanishingH) :
    q₁ = q₂ := by
  have hvan : ∀ q : VerifierQuery shape.k F G,
      q ∈ assembleQueries vk instanceCommitment ps ch →
      q.commId = CommitmentId.vanishingH →
      q ∈ vanishingQueries (k := shape.k) ch.x
        (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces))
        (expectedHEval (allExpressions vk ps ch
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2) ch.y
          (ch.x ^ vk.n))
        ps.vanishingRandom ps.vanishingRandomEval := by
    intro q hq hv
    simp only [assembleQueries, List.mem_append] at hq
    rcases hq with (((h | h) | h) | h)
    · -- per-sub-proof block
      rw [List.mem_flatten] at h
      obtain ⟨l, hlof, hql⟩ := h
      rw [List.mem_ofFn] at hlof
      obtain ⟨p, rfl⟩ := hlof
      simp only [List.mem_append] at hql
      rcases hql with ((hql | hql) | hql) | hql
      · obtain ⟨n, hn⟩ := columnQueries_commId_form hql; rw [hv] at hn; exact absurd hn (by simp)
      · obtain ⟨n, hn⟩ := columnQueries_commId_form hql; rw [hv] at hn; exact absurd hn (by simp)
      · obtain ⟨n, hn⟩ := permutationQueries_commId_form hql; rw [hv] at hn
        exact absurd hn (by simp)
      · obtain ⟨n, hn | hn | hn⟩ := lookupQueries_commId_form hql <;>
          (rw [hv] at hn; exact absurd hn (by simp))
    · obtain ⟨n, hn⟩ := columnQueries_commId_form h; rw [hv] at hn; exact absurd hn (by simp)
    · obtain ⟨n, hn⟩ := permutationCommonQueries_commId_form h; rw [hv] at hn
      exact absurd hn (by simp)
    · exact h
  have h1 := hvan q₁ hq₁ hv₁
  have h2 := hvan q₂ hq₂ hv₂
  simp only [vanishingQueries, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  rcases h1 with rfl | rfl
  · rcases h2 with rfl | rfl
    · rfl
    · exact CommitmentId.noConfusion hv₂
  · exact CommitmentId.noConfusion hv₁

/-- Whether the flat query list contains two queries for the same commitment slot at the same
point. Halo2 rejects this (`None`, mapped to `OpeningError`), even when the two evaluations
agree. -/
def hasDuplicateCommitmentPoint {k : ℕ} {F G : Type*} [DecidableEq F] :
    List (VerifierQuery k F G) → Bool
  | [] => false
  | q :: qs =>
      qs.any (fun r => decide (r.commId = q.commId ∧ r.point = q.point))
        || hasDuplicateCommitmentPoint qs

/-- On the non-duplicate path, a commitment-slot/opening-point pair identifies at most one query.
This is the semantic form of the guard used by grouping eval faithfulness below. -/
theorem query_eq_of_noDuplicateCommitmentPoint {k : ℕ} {F G : Type*} [DecidableEq F]
    {queries : List (VerifierQuery k F G)}
    (hdup : hasDuplicateCommitmentPoint queries = false)
    {q₁ q₂ : VerifierQuery k F G} (hq₁ : q₁ ∈ queries) (hq₂ : q₂ ∈ queries)
    (hid : q₁.commId = q₂.commId) (hpoint : q₁.point = q₂.point) :
    q₁ = q₂ := by
  induction queries generalizing q₁ q₂ with
  | nil => exact absurd hq₁ List.not_mem_nil
  | cons q queries ih =>
      simp only [hasDuplicateCommitmentPoint, Bool.or_eq_false_iff, List.any_eq_false] at hdup
      rcases hdup with ⟨hhead, htail⟩
      rcases List.mem_cons.mp hq₁ with hq₁ | hq₁
      · subst q₁
        rcases List.mem_cons.mp hq₂ with hq₂ | hq₂
        · exact hq₂.symm
        · have hn := hhead q₂ hq₂
          exfalso
          apply hn
          simp [hid, hpoint]
      · rcases List.mem_cons.mp hq₂ with hq₂ | hq₂
        · subst q₂
          have hn := hhead q₁ hq₁
          exfalso
          apply hn
          simp [hid, hpoint]
        · exact ih htail hq₁ hq₂ hid hpoint

/-- Two everywhere-defined `filterMap` projections preserve the position of a selected source
element when the first projection identifies it uniquely. -/
theorem filterMap_getD_idxOf {α β γ : Type*} [DecidableEq β]
    {l : List α} {f : α → Option β} {g : α → Option γ}
    {a : α} {b : β} {c d : γ}
    (ha : a ∈ l)
    (hfAll : ∀ x ∈ l, (f x).isSome)
    (hgAll : ∀ x ∈ l, (g x).isSome)
    (hf : f a = some b) (hg : g a = some c)
    (huniq : ∀ x ∈ l, f x = some b → x = a) :
    (l.filterMap g).getD ((l.filterMap f).idxOf b) d = c := by
  induction l with
  | nil => exact absurd ha List.not_mem_nil
  | cons x xs ih =>
      have hfx := hfAll x (List.mem_cons_self ..)
      have hgx := hgAll x (List.mem_cons_self ..)
      rcases hfxEq : f x with _ | fx
      · rw [hfxEq] at hfx
        exact absurd hfx (by simp)
      rcases hgxEq : g x with _ | gx
      · rw [hgxEq] at hgx
        exact absurd hgx (by simp)
      by_cases hxa : x = a
      · subst x
        simp [hf, hg]
      · have ha' : a ∈ xs := (List.mem_cons.mp ha).resolve_left (Ne.symm hxa)
        have hfxb : fx ≠ b := by
          intro heq
          apply hxa
          exact huniq x (List.mem_cons_self ..) (hfxEq.trans (congrArg some heq))
        have hi := ih ha'
          (fun y hy => hfAll y (List.mem_cons_of_mem _ hy))
          (fun y hy => hgAll y (List.mem_cons_of_mem _ hy))
          (fun y hy => huniq y (List.mem_cons_of_mem _ hy))
        simp only [List.filterMap_cons, hfxEq, hgxEq]
        rw [List.idxOf_cons_ne _ hfxb, List.getD_cons_succ, hi]

/-- `find?` returns a present satisfying element when it is the only satisfying value in the list. -/
theorem find?_eq_some_of_unique {α : Type*} {l : List α} {p : α → Bool} {a : α}
    (ha : a ∈ l) (hpa : p a = true)
    (huniq : ∀ x ∈ l, p x = true → x = a) :
    l.find? p = some a := by
  induction l with
  | nil => exact absurd ha List.not_mem_nil
  | cons x xs ih =>
      by_cases hx : p x = true
      · have hxa := huniq x (List.mem_cons_self ..) hx
        subst x
        exact List.find?_cons_of_pos hpa
      · rw [List.find?_cons_of_neg hx]
        apply ih
        · exact (List.mem_cons.mp ha).resolve_left
            (fun h => hx (h ▸ hpa))
        · exact fun y hy => huniq y (List.mem_cons_of_mem _ hy)

/-- A query's per-commitment data entry records its claimed evaluation at the position of its
opening point.  The non-duplicate guard makes the `find?` used by grouping faithful to that query. -/
theorem cisData_query_eval {k : ℕ} {F G : Type*} [DecidableEq F] [Zero F]
    (queries : List (VerifierQuery k F G))
    {q : VerifierQuery k F G} (hq : q ∈ queries)
    (hdup : hasDuplicateCommitmentPoint queries = false)
    {cd : CommitmentId × CommitmentRef k F G × List ℕ × List F}
    (hcd : cd ∈ cisData queries) (hid : cd.1 = q.commId) :
    cd.2.2.2.getD
      ((cd.2.2.1.filterMap fun i => (cisPts queries)[i]?).idxOf q.point) 0 = q.eval := by
  classical
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcd
  simp only at hid ⊢
  let qs := queries.filter fun q' => decide (q'.commId = c.1)
  let idxSet := (List.range (cisPts queries).length).filter fun i =>
    (qs.map fun q' => cisPIdx queries q'.point).contains i
  have hqQs : q ∈ qs := by
    exact List.mem_filter.mpr ⟨hq, by simp [hid]⟩
  have hqPts : q.point ∈ cisPts queries :=
    mem_dedup_foldl queries (·.point) [] hq
  have hpointIdx : cisPIdx queries q.point < (cisPts queries).length :=
    List.findIdx_lt_length_of_exists ⟨q.point, hqPts, by simp⟩
  have hidx : cisPIdx queries q.point ∈ idxSet := by
    simp only [idxSet, List.mem_filter, List.mem_range]
    exact ⟨hpointIdx, (List.contains_iff_mem).mpr
      (List.mem_map.mpr ⟨q, hqQs, rfl⟩)⟩
  have hptsNodup : (cisPts queries).Nodup := by
    exact nodup_dedup_foldl queries (·.point) [] List.nodup_nil
  have hpointGet : (cisPts queries)[cisPIdx queries q.point]? = some q.point :=
    getElem?_findIdx_self hqPts
  have hpointUnique : ∀ i ∈ idxSet,
      (cisPts queries)[i]? = some q.point → i = cisPIdx queries q.point := by
    intro i hi hget
    rw [List.mem_filter, List.mem_range] at hi
    have heq : (⟨i, hi.1⟩ : Fin _) = ⟨cisPIdx queries q.point, hpointIdx⟩ := by
      apply List.nodup_iff_injective_getElem.mp hptsNodup
      rw [List.getElem?_eq_getElem hi.1] at hget
      rw [List.getElem?_eq_getElem hpointIdx] at hpointGet
      exact Option.some.inj (hget.trans hpointGet.symm)
    exact congrArg Fin.val heq
  have heveryPoint : ∀ i ∈ idxSet, ((cisPts queries)[i]?).isSome := by
    intro i hi
    rw [List.mem_filter, List.mem_range] at hi
    rw [List.getElem?_eq_getElem hi.1]
    simp
  have heveryEval : ∀ i ∈ idxSet,
      ((qs.find? fun q' => decide (cisPIdx queries q'.point = i)).map (·.eval)).isSome := by
    intro i hi
    rw [List.mem_filter] at hi
    obtain ⟨q', hq', hq'i⟩ := List.mem_map.mp ((List.contains_iff_mem).mp hi.2)
    rw [Option.isSome_map, List.find?_isSome]
    exact ⟨q', hq', by simp [hq'i]⟩
  have hfind : (qs.find? fun q' =>
      decide (cisPIdx queries q'.point = cisPIdx queries q.point)) = some q := by
    apply find?_eq_some_of_unique hqQs (by simp)
    intro q' hq' hpred
    simp only [decide_eq_true_eq] at hpred
    have hq'query := (List.mem_filter.mp hq').1
    have hq'id : q'.commId = q.commId := by
      have h := (List.mem_filter.mp hq').2
      simp only [decide_eq_true_eq] at h
      exact h.trans hid
    have hq'Pts : q'.point ∈ cisPts queries :=
      mem_dedup_foldl queries (·.point) [] hq'query
    have hq'get := getElem?_findIdx_self hq'Pts
    change (cisPts queries)[cisPIdx queries q'.point]? = some q'.point at hq'get
    rw [hpred] at hq'get
    have hq'point : q'.point = q.point :=
      Option.some.inj (hq'get.symm.trans hpointGet)
    exact query_eq_of_noDuplicateCommitmentPoint hdup hq'query hq hq'id hq'point
  change
    (idxSet.filterMap fun i =>
      (qs.find? fun q' => decide (cisPIdx queries q'.point = i)).map (·.eval)).getD
      ((idxSet.filterMap fun i => (cisPts queries)[i]?).idxOf q.point) 0 = q.eval
  exact filterMap_getD_idxOf hidx heveryPoint heveryEval hpointGet
    (by rw [hfind]; rfl) hpointUnique

/-- Rejecting version of `constructIntermediateSets`, matching halo2's `Option` guard for duplicate
queries with the same commitment slot and point. -/
def constructIntermediateSets? {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G)) : Option (MultiopenGrouped k F G) :=
  if hasDuplicateCommitmentPoint queries then none else some (constructIntermediateSets queries)

/-- The non-duplicate path routes every query with its slot, point, and claimed evaluation. -/
theorem constructIntermediateSets_query_routed {k : ℕ} {F G : Type*}
    [DecidableEq F] [DecidableEq G] [Zero F] [Zero G]
    (queries : List (VerifierQuery k F G)) {q : VerifierQuery k F G}
    (hq : q ∈ queries) (hdup : hasDuplicateCommitmentPoint queries = false) :
    ∃ si, si < (constructIntermediateSets queries).sets.length ∧
      ∃ m, m < ((constructIntermediateSets queries).sets.getD si []).length ∧
        ((constructIntermediateSets queries).ids.getD si []).getD m .vanishingH = q.commId ∧
        q.point ∈ (constructIntermediateSets queries).points.getD si [] ∧
        (((constructIntermediateSets queries).sets.getD si []).getD m (.point 0, [])).2.getD
          (((constructIntermediateSets queries).points.getD si []).idxOf q.point) 0 = q.eval := by
  classical
  obtain ⟨e, he, heid⟩ := cisComms_fold_covers queries [] hq
  rcases cisComms_fold_prov queries [] he with hnil | ⟨q', hq', rfl⟩
  · exact absurd hnil List.not_mem_nil
  let qs := queries.filter fun r => decide (r.commId = q'.commId)
  let idxSet := (List.range (cisPts queries).length).filter fun i =>
    (qs.map fun r => cisPIdx queries r.point).contains i
  let evals := idxSet.filterMap fun i =>
    (qs.find? fun r => decide (cisPIdx queries r.point = i)).map (·.eval)
  let cd : CommitmentId × CommitmentRef k F G × List ℕ × List F :=
    (q'.commId, q'.commitment, idxSet, evals)
  have hcd : cd ∈ cisData queries := by
    refine List.mem_map.mpr ⟨(q'.commId, q'.commitment), he, ?_⟩
    rfl
  have hcdid : cd.1 = q.commId := heid
  have hcdeval := cisData_query_eval queries hq hdup hcd hcdid
  have hsetmem : cd.2.2.1 ∈ cisSetList queries := by
    have h := mem_dedup_foldl (cisData queries) (fun x => x.2.2.1) ([] : List (List ℕ)) hcd
    simpa using h
  let si := (cisSetList queries).findIdx fun x => decide (x = cd.2.2.1)
  have hsiLt : si < (cisSetList queries).length :=
    List.findIdx_lt_length_of_exists ⟨cd.2.2.1, hsetmem, by simp⟩
  have hsiGet : (cisSetList queries)[si]? = some cd.2.2.1 :=
    getElem?_findIdx_self hsetmem
  have hrouted : cd ∈ cisRouted queries si := by
    rw [cisRouted]
    refine List.mem_filter.mpr ⟨List.mem_reverse.mpr hcd, ?_⟩
    simp [si]
  obtain ⟨m, hm, hmget⟩ := List.mem_iff_getElem.mp hrouted
  have hsetLt : si < (constructIntermediateSets queries).sets.length := by
    show si < ((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun data => (data.2.1, data.2.2.2)).length
    rw [List.length_map, List.length_range]
    exact hsiLt
  have hmembers :
      (constructIntermediateSets queries).sets.getD si []
        = (cisRouted queries si).map fun data => (data.2.1, data.2.2.2) := by
    show ((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun data => (data.2.1, data.2.2.2)).getD si []
        = _
    have hi : si < ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map fun data => (data.2.1, data.2.2.2)).length := by
      rw [List.length_map, List.length_range]
      exact hsiLt
    rw [List.getD_eq_getElem _ _ hi, List.getElem_map, List.getElem_range]
  have hmemLt : m < ((constructIntermediateSets queries).sets.getD si []).length := by
    rw [hmembers, List.length_map]
    exact hm
  have hids :
      (constructIntermediateSets queries).ids.getD si []
        = (cisRouted queries si).map (·.1) := by
    show ((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map (·.1)).getD si [] = _
    have hi : si < ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map (·.1)).length := by
      rw [List.length_map, List.length_range]
      exact hsiLt
    rw [List.getD_eq_getElem _ _ hi, List.getElem_map, List.getElem_range]
  have hid :
      ((constructIntermediateSets queries).ids.getD si []).getD m .vanishingH = q.commId := by
    rw [hids, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm),
      List.getElem_map, hmget]
    exact hcdid
  have hpoint :
      q.point ∈ (constructIntermediateSets queries).points.getD si [] :=
    constructIntermediateSets_point_mem queries hq
      (by rw [constructIntermediateSets_sets_ids_aligned queries si]; exact hmemLt) hid
  have hpoints :
      (constructIntermediateSets queries).points.getD si []
        = cd.2.2.1.filterMap fun i => (cisPts queries)[i]? := by
    show ((cisSetList queries).map fun s =>
      s.filterMap fun i => (cisPts queries)[i]?).getD si [] = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hsiGet]
    rfl
  have hmember :
      ((constructIntermediateSets queries).sets.getD si []).getD m (.point 0, [])
        = (cd.2.1, cd.2.2.2) := by
    rw [hmembers, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm),
      List.getElem_map, hmget]
  refine ⟨si, hsetLt, m, hmemLt, hid, hpoint, ?_⟩
  rw [hmember, hpoints]
  exact hcdeval

/-- A query routed to any member carrying its commitment identity reads back its own claimed
evaluation.  This is the reusable eval-faithfulness companion to
`constructIntermediateSets_point_mem`. -/
theorem constructIntermediateSets_query_eval {k : ℕ} {F G : Type*}
    [DecidableEq F] [DecidableEq G] [Zero F] [Zero G]
    (queries : List (VerifierQuery k F G)) {q : VerifierQuery k F G}
    (hq : q ∈ queries) (hdup : hasDuplicateCommitmentPoint queries = false)
    {si m : ℕ}
    (hlt : m < ((constructIntermediateSets queries).ids.getD si []).length)
    (hid : ((constructIntermediateSets queries).ids.getD si []).getD m .vanishingH
      = q.commId) :
    (((constructIntermediateSets queries).sets.getD si []).getD m (.point 0, [])).2.getD
      (((constructIntermediateSets queries).points.getD si []).idxOf q.point) 0 = q.eval := by
  classical
  have hsiIds : si < (constructIntermediateSets queries).ids.length := by
    by_contra hn
    have hge := Nat.le_of_not_gt hn
    rw [List.getD_eq_default _ _ hge] at hlt
    simp at hlt
  have hsiSet : si < (cisSetList queries).length := by
    change si < ((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map (·.1)).length at hsiIds
    rw [List.length_map, List.length_range] at hsiIds
    exact hsiIds
  have hids :
      (constructIntermediateSets queries).ids.getD si []
        = (cisRouted queries si).map (·.1) := by
    show ((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map (·.1)).getD si [] = _
    have hi : si < ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map (·.1)).length := by
      rw [List.length_map, List.length_range]
      exact hsiSet
    rw [List.getD_eq_getElem _ _ hi, List.getElem_map, List.getElem_range]
  have hm : m < (cisRouted queries si).length := by
    rw [hids, List.length_map] at hlt
    exact hlt
  let cd := (cisRouted queries si)[m]
  have hcdRouted : cd ∈ cisRouted queries si := List.getElem_mem hm
  have hcdData : cd ∈ cisData queries := by
    have h := (List.mem_filter.mp hcdRouted).1
    exact List.mem_reverse.mp h
  have hcdId : cd.1 = q.commId := by
    rw [hids, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm),
      List.getElem_map] at hid
    exact hid
  have hcdeval := cisData_query_eval queries hq hdup hcdData hcdId
  have hrouteEq : (cisSetList queries).findIdx
      (fun x => decide (x = cd.2.2.1)) = si := by
    have h := (List.mem_filter.mp hcdRouted).2
    simpa [cisRouted] using h
  have hcdSetMem : cd.2.2.1 ∈ cisSetList queries := by
    have h := mem_dedup_foldl (cisData queries) (fun x => x.2.2.1)
      ([] : List (List ℕ)) hcdData
    simpa using h
  have hsetGet : (cisSetList queries)[si]? = some cd.2.2.1 := by
    rw [← hrouteEq]
    exact getElem?_findIdx_self hcdSetMem
  have hmembers :
      (constructIntermediateSets queries).sets.getD si []
        = (cisRouted queries si).map fun data => (data.2.1, data.2.2.2) := by
    show ((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun data => (data.2.1, data.2.2.2)).getD si [] = _
    have hi : si < ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map fun data => (data.2.1, data.2.2.2)).length := by
      rw [List.length_map, List.length_range]
      exact hsiSet
    rw [List.getD_eq_getElem _ _ hi, List.getElem_map, List.getElem_range]
  have hmember :
      ((constructIntermediateSets queries).sets.getD si []).getD m (.point 0, [])
        = (cd.2.1, cd.2.2.2) := by
    rw [hmembers, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm),
      List.getElem_map]
  have hpoints :
      (constructIntermediateSets queries).points.getD si []
        = cd.2.2.1.filterMap fun i => (cisPts queries)[i]? := by
    show ((cisSetList queries).map fun s =>
      s.filterMap fun i => (cisPts queries)[i]?).getD si [] = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hsetGet]
    rfl
  rw [hmember, hpoints]
  exact hcdeval

/--
The grouped commitment and identity views at one member position come from the same flat query.
This indexed provenance statement preserves the `CommitmentId` aligned with the group element.
-/
theorem constructIntermediateSets_member_provenance {k : ℕ} {F G : Type*}
    [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G))
    (i m : ℕ)
    (hi : i < (constructIntermediateSets queries).sets.length)
    (hm : m < ((constructIntermediateSets queries).sets.getD i []).length)
    (defaultMember : CommitmentRef k F G × List F)
    (defaultId : CommitmentId) :
    ∃ q ∈ queries,
      (((constructIntermediateSets queries).sets.getD i []).getD m defaultMember).1 =
          q.commitment ∧
        ((constructIntermediateSets queries).ids.getD i []).getD m defaultId =
          q.commId := by
  classical
  have hiSetList : i < (cisSetList queries).length := by
    change i < ((List.range (cisSetList queries).length).map fun si =>
      (cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2)).length at hi
    simpa using hi
  have hsets :
      (constructIntermediateSets queries).sets.getD i [] =
        (cisRouted queries i).map fun cd => (cd.2.1, cd.2.2.2) := by
    change ((List.range (cisSetList queries).length).map fun si =>
      (cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2)).getD i [] = _
    rw [List.getD_eq_getElem _ _ (by simpa using hiSetList),
      List.getElem_map, List.getElem_range]
  have hids :
      (constructIntermediateSets queries).ids.getD i [] =
        (cisRouted queries i).map (·.1) := by
    change ((List.range (cisSetList queries).length).map fun si =>
      (cisRouted queries si).map (·.1)).getD i [] = _
    rw [List.getD_eq_getElem _ _ (by simpa using hiSetList),
      List.getElem_map, List.getElem_range]
  have hmRouted : m < (cisRouted queries i).length := by
    rw [hsets, List.length_map] at hm
    exact hm
  let cd := (cisRouted queries i)[m]
  have hcdRouted : cd ∈ cisRouted queries i :=
    List.getElem_mem hmRouted
  have hcdData : cd ∈ cisData queries := by
    exact List.mem_reverse.mp (List.mem_filter.mp hcdRouted).1
  obtain ⟨c, hc, hcd⟩ := List.mem_map.mp hcdData
  rcases cisComms_fold_prov queries [] hc with hnil | ⟨q, hq, hcq⟩
  · exact absurd hnil List.not_mem_nil
  · have hcommitment : cd.2.1 = q.commitment :=
      (congrArg (fun entry => entry.2.1) hcd).symm.trans
        (congrArg (fun entry => entry.2) hcq)
    have hidentity : cd.1 = q.commId :=
      (congrArg (fun entry => entry.1) hcd).symm.trans
        (congrArg (fun entry => entry.1) hcq)
    refine ⟨q, hq, ?_, ?_⟩
    · rw [hsets, List.getD_eq_getElem _ _ (by simpa using hmRouted),
        List.getElem_map]
      simpa [cd] using hcommitment
    · rw [hids, List.getD_eq_getElem _ _ (by simpa using hmRouted),
        List.getElem_map]
      simpa [cd] using hidentity

/-- Rejecting version of `assembleOpening`. Halo2 derives the number of `u` evaluations from the grouped
point sets and reads exactly that many scalars; a mismatch means the typed proof string is not the deployed
verifier's read stream. -/
def assembleOpening? {k : ℕ} {F G : Type*} [Field F] (x1 x2 x3 x4 : F) (qPrime : G) (u : List F)
    (grouped : MultiopenGrouped k F G) (incoming : Msm k F G) : Option (Msm k F G × F) :=
  if u.length = grouped.sets.length ∧ grouped.points.length = grouped.sets.length then
    some (assembleOpening x1 x2 x3 x4 qPrime u grouped incoming)
  else
    none

/-- Rejecting version of `assembleFinalMsm`, using the deployed verifier's dynamic `u` count check. -/
def assembleFinalMsm? {shape : Shape} {F G : Type*} [Field F] (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (grouped : MultiopenGrouped shape.k F G) : Option (Msm shape.k F G) :=
  match assembleOpening? ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
      grouped (Msm.zero shape.k F G) with
  | some opened =>
      some <| ipaFold ch.x3 opened.2 ps.ipaC ps.ipaF ch.xi ch.z (List.ofFn ch.ipaRound) ps.ipaS
        (List.ofFn ps.ipaRounds) opened.1
  | none => none

/-- The multiopen inverse factors are defined only when the IPA challenge `x₃` is not one of the opened
points in any derived point set. In the deployed verifier this case is a panic, not an error return
(`(x₃ - point).invert().unwrap()` in `multiopen/verifier.rs`); the Lean rejection abstracts that crash —
both are non-accepting, which is what soundness consumes. `card_multiopenPanic_le` bounds the offending
`x₃`: at most one per opened point, a negligible proportion of challenges. -/
def multiopenPointsAvoidX3 {k : ℕ} {F G : Type*} [DecidableEq F] (x3 : F)
    (grouped : MultiopenGrouped k F G) : Bool :=
  grouped.points.all fun pts => pts.all fun point => decide (x3 ≠ point)

/-- At most one bad `x₃` per opened point can trigger multiopen inversion failure. -/
theorem card_multiopenPanic_le {k : ℕ} {F G : Type*} [DecidableEq F] [Fintype F]
    (grouped : MultiopenGrouped k F G) :
    (Finset.univ.filter (fun x3 : F => multiopenPointsAvoidX3 x3 grouped = false)).card
      ≤ grouped.points.flatten.length := by
  -- the panicking `x₃` embed in the flattened list of opened points
  refine le_trans (Finset.card_le_card ?_) (List.toFinset_card_le _)
  intro x3 hx3
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx3
  rw [List.mem_toFinset]
  -- an `x₃` that avoided every opened point would not panic, contradicting `avoid = false`
  by_contra hnot
  have hAvoid : multiopenPointsAvoidX3 x3 grouped = true := by
    simp only [multiopenPointsAvoidX3, List.all_eq_true, decide_eq_true_eq]
    intro pts hpts point hpoint hx
    exact hnot (List.mem_flatten.mpr ⟨pts, hpts, by rw [hx]; exact hpoint⟩)
  rw [hAvoid] at hx3
  exact Bool.noConfusion hx3

/-- At most `n` field elements satisfy `x^n = 1` and trigger vanishing inversion failure. -/
theorem card_vanishingPanic_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (hn : 0 < n) :
    (Finset.univ.filter (fun x : F => x ^ n = 1)).card ≤ n := by
  -- the bad `x` are the roots of `Xⁿ - 1`, at most `n` of them
  refine le_trans (Finset.card_le_card ?_)
    (le_trans (Multiset.toFinset_card_le _) (Polynomial.card_nthRoots n 1))
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
  exact hx

/-- `permutation_product_last_eval` is read by halo2 for every non-last permutation set and is absent for
the last set. This checks the typed proof string follows that read schedule. -/
def permutationLastEvalsWellFormed {shape : Shape} {F G : Type*} (ps : ProofString shape F G) : Bool :=
  (List.ofFn (fun p : Fin shape.numProofs =>
    (List.ofFn (fun s : Fin shape.numPermutationSets =>
      if s.val + 1 = shape.numPermutationSets then
        match (ps.permutationSetEvals p s).lastEval with
        | none => true
        | some _ => false
      else
        match (ps.permutationSetEvals p s).lastEval with
        | some _ => true
        | none => false)).all id)).all id

/-- Typed proof-string well-formedness that affects deployed verifier control flow. Byte-level
decoding is outside this layer; `ProofString` starts after it. -/
def proofStringWellFormed {shape : Shape} {F G : Type*} (ps : ProofString shape F G) : Bool :=
  permutationLastEvalsWellFormed ps

/-- The deployed verifier MSM assembly with the rejection paths modeled:
`construct_intermediate_sets` can fail on duplicate commitment/point queries, the number of prover
`u` evaluations must equal the derived number of point sets, inverse denominators must be nonzero, and
typed proof fields must follow Halo2's read schedule.

Two of these rejections abstract deployed *panics*, not error returns: at `xⁿ = 1` halo2 crashes on
`(xn - 1).invert().unwrap()` (`vanishing/verifier.rs`), and at `x₃` hitting an opened point on
`(x₃ - point).invert().unwrap()` (`multiopen/verifier.rs`). Both strike a negligible proportion of
challenges (`card_vanishingPanic_le`, `card_multiopenPanic_le`) and are non-accepting either way, which is
the property the soundness layer consumes; the model just renders "crash" as `none`.

Halo2 reads one `u` per derived point set; `assemble?` checks that count against the shape-fixed
`multiopenU`. The counts agree at the deployed key because grouping is fixed away from rejected
collisions, and the duplicate guard rejects the only collapsing value, `x = 0`. The derived-key
query-count lemmas in `Keygen/Pipeline.lean` also keep layout/evaluation zips from truncating. -/
def assemble? {shape : Shape} {F G : Type*} [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) :
    Option (Msm shape.k F G) :=
  if proofStringWellFormed ps then
    if ch.x ^ vk.n = (1 : F) then
      none
    else
      match constructIntermediateSets? (assembleQueries vk instanceCommitment ps ch) with
      | some grouped =>
          if multiopenPointsAvoidX3 ch.x3 grouped then
            assembleFinalMsm? ps ch grouped
          else
            none
      | none => none
  else
    none

/-- The checked assembler depends on instance commitments only at columns named by the VK's
instance-query layout. -/
theorem assemble?_congr_instanceCommitment
    {shape : Shape} {F G : Type*} [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G)
    (instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (h : ∀ p column rotation, (column, rotation) ∈ vk.instanceQueryLayout →
      instanceCommitment p column = instanceCommitment' p column) :
    assemble? vk instanceCommitment ps ch = assemble? vk instanceCommitment' ps ch := by
  unfold assemble?
  rw [assembleQueries_congr_instanceCommitment vk instanceCommitment instanceCommitment' ps ch h]

/-- If the VK's instance-query layout is in range, the checked assembler depends only on the
configured finite rectangle of instance commitments. -/
theorem assemble?_congr_instanceCommitment_of_layout_bounded
    {shape : Shape} {F G : Type*} [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G)
    (instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (hCommitment : ∀ p column, column < shape.numInstanceColumns →
      instanceCommitment p column = instanceCommitment' p column)
    (hLayout : ∀ column rotation, (column, rotation) ∈ vk.instanceQueryLayout →
      column < shape.numInstanceColumns) :
    assemble? vk instanceCommitment ps ch = assemble? vk instanceCommitment' ps ch := by
  apply assemble?_congr_instanceCommitment vk instanceCommitment instanceCommitment' ps ch
  intro p column rotation hmem
  exact hCommitment p column (hLayout column rotation hmem)

/-- The full verifier MSM, total form: build the opening queries, derive the multiopen grouping
(`constructIntermediateSets`), then assemble (`assembleFinalMsm`) — the deployed fingerprint as a
pure function of `(vk, ps, ch)`. Wraps `assemble?`, returning the zero MSM on the proof data it
rejects; kept for the algebraic fingerprint lemmas.

**Warning:** the zero-MSM fallback *evaluates to `0`* — the accept value. Never define acceptance as
`(assemble …).eval urs = 0`: on every rejection path that predicate holds vacuously, i.e. the total
wrapper accepts malformed input. Acceptance must go through `assemble?` (as `DeployedAccepts` does),
where rejection is `none`. -/
def assemble {shape : Shape} {F G : Type*} [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) :
    Msm shape.k F G :=
  (assemble? vk instanceCommitment ps ch).getD (Msm.zero shape.k F G)

/-- An injective total option map preserves source positions through `filterMap`. -/
private theorem filterMap_idxOf_of_forall_isSome {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome) →
      (∀ x ∈ l, ∀ x' ∈ l, f x = f x' → x = x') →
      ∀ {j : α} {b : β}, j ∈ l → f j = some b →
      (l.filterMap f).idxOf b = l.idxOf j := by
  intro l
  induction l with
  | nil => intro _ _ j b hj _; exact absurd hj List.not_mem_nil
  | cons a t ih =>
      intro hsome hinj j b hj hfj
      rcases ha : f a with _ | ba
      · exact absurd (hsome a (List.mem_cons_self ..)) (by simp [ha])
      rw [List.filterMap_cons, ha]
      by_cases haj : a = j
      · subst haj
        rw [ha] at hfj
        obtain rfl := Option.some.inj hfj
        simp
      · have hjt : j ∈ t := (List.mem_cons.mp hj).resolve_left (fun h => haj h.symm)
        have hba : ba ≠ b := fun hbb =>
          haj (hinj a (List.mem_cons_self ..) j hj (by rw [ha, hfj, hbb]))
        rw [List.idxOf_cons_ne _ hba, List.idxOf_cons_ne _ haj,
          ih (fun x hx => hsome x (List.mem_cons_of_mem _ hx))
            (fun x hx x' hx' => hinj x (List.mem_cons_of_mem _ hx) x'
              (List.mem_cons_of_mem _ hx')) hjt hfj]

/-- An everywhere-defined `filterMap` read at a source element's first position gives that
element's image. -/
private theorem filterMap_getD_idxOf_of_forall_isSome {α β : Type*} [DecidableEq α] (d : β)
    {g : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, (g x).isSome) →
      ∀ {j : α} {c : β}, j ∈ l → g j = some c →
      (l.filterMap g).getD (l.idxOf j) d = c := by
  intro l
  induction l with
  | nil => intro _ j c hj _; exact absurd hj List.not_mem_nil
  | cons a t ih =>
      intro hsome j c hj hgj
      rcases ha : g a with _ | ca
      · exact absurd (hsome a (List.mem_cons_self ..)) (by simp [ha])
      rw [List.filterMap_cons, ha]
      by_cases haj : a = j
      · subst haj
        rw [ha] at hgj
        obtain rfl := Option.some.inj hgj
        simp
      · have hjt : j ∈ t := (List.mem_cons.mp hj).resolve_left (fun h => haj h.symm)
        rw [List.idxOf_cons_ne _ haj]
        simpa using ih (fun x hx => hsome x (List.mem_cons_of_mem _ hx)) hjt hgj

open Classical in
/-- Every query is routed while preserving its commitment, point, and claimed evaluation. -/
theorem constructIntermediateSets_comm_routed {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) {q : VerifierQuery k F G}
    (hq : q ∈ queries)
    (hdet : ∀ q' ∈ queries, q'.commId = q.commId → q'.point = q.point → q'.eval = q.eval)
    (hcommit : ∀ q' ∈ queries, q'.commId = q.commId → q'.commitment = q.commitment) :
    ∃ i, i < (constructIntermediateSets queries).sets.length ∧
      ∃ m, m < ((constructIntermediateSets queries).sets.getD i []).length ∧
        (∀ c₀, ((constructIntermediateSets queries).ids.getD i []).getD m c₀ = q.commId) ∧
        (∀ d₀, (((constructIntermediateSets queries).sets.getD i []).getD m d₀).1
          = q.commitment) ∧
        q.point ∈ (constructIntermediateSets queries).points.getD i [] ∧
        ∀ d₀ (z₀ : F), (((constructIntermediateSets queries).sets.getD i []).getD m d₀).2.getD
            (((constructIntermediateSets queries).points.getD i []).idxOf q.point) z₀
          = q.eval := by
  classical
  -- the slot is keyed by the commitment dedup, with some curve value
  obtain ⟨e, he, hek⟩ := cisComms_fold_covers queries [] hq
  have hecommit : e.2 = q.commitment := by
    rcases cisComms_fold_prov queries [] he with h0 | ⟨q', hq', heq⟩
    · exact absurd h0 List.not_mem_nil
    · rw [heq] at hek ⊢
      exact hcommit q' hq' hek
  -- its per-commitment data entry
  have hcd : (e.1, e.2,
      (List.range (cisPts queries).length).filter
        (fun i => ((queries.filter (fun q'' => decide (q''.commId = e.1))).map
          (fun q' => cisPIdx queries q'.point)).contains i),
      ((List.range (cisPts queries).length).filter
        (fun i => ((queries.filter (fun q'' => decide (q''.commId = e.1))).map
          (fun q' => cisPIdx queries q'.point)).contains i)).filterMap
        (fun i => ((queries.filter (fun q'' => decide (q''.commId = e.1))).find?
          (fun q' => decide (cisPIdx queries q'.point = i))).map (·.eval)))
      ∈ cisData queries :=
    List.mem_map.mpr ⟨e, he, rfl⟩
  set qs := queries.filter (fun q'' => decide (q''.commId = e.1)) with hqs
  set idxSet := (List.range (cisPts queries).length).filter
    (fun i => (qs.map (fun q' => cisPIdx queries q'.point)).contains i) with hidxSet
  set evals := idxSet.filterMap
    (fun i => (qs.find? (fun q' => decide (cisPIdx queries q'.point = i))).map (·.eval))
    with hevals
  -- `q` itself is one of the slot's queries
  have hqmem : q ∈ qs := List.mem_filter.mpr ⟨hq, by rw [decide_eq_true_eq]; exact hek.symm⟩
  -- the point index of `q.point`, and its membership in the entry's index set
  set j := cisPIdx queries q.point with hj
  have hjlt : j < (cisPts queries).length :=
    List.findIdx_lt_length_of_exists
      ⟨q.point, mem_dedup_foldl queries (·.point) [] hq, by simp⟩
  have hjget : (cisPts queries)[j]? = some q.point :=
    getElem?_findIdx_self (mem_dedup_foldl queries (·.point) [] hq)
  have hjmem : j ∈ idxSet := by
    rw [hidxSet]
    refine List.mem_filter.mpr ⟨List.mem_range.mpr hjlt, ?_⟩
    exact (List.contains_iff_mem).mpr (List.mem_map.mpr ⟨q, hqmem, rfl⟩)
  -- both extractions are everywhere defined on the index set
  have hfsome : ∀ i ∈ idxSet, ((cisPts queries)[i]?).isSome := by
    intro i hi
    rw [hidxSet, List.mem_filter, List.mem_range] at hi
    rw [List.getElem?_eq_getElem hi.1]
    exact Option.isSome_some
  have hgsome : ∀ i ∈ idxSet,
      ((qs.find? (fun q' => decide (cisPIdx queries q'.point = i))).map (·.eval)).isSome := by
    intro i hi
    rw [hidxSet, List.mem_filter] at hi
    have hxq := (List.contains_iff_mem).mp hi.2
    obtain ⟨q', hq', hq'i⟩ := List.mem_map.mp hxq
    have hfind : (qs.find? (fun q'' => decide (cisPIdx queries q''.point = i))).isSome := by
      rw [List.find?_isSome]
      exact ⟨q', hq', by simp [hq'i]⟩
    simpa using hfind
  -- the point extraction is injective on the index set (the internal points list is `Nodup`)
  have hfinj : ∀ i ∈ idxSet, ∀ i' ∈ idxSet,
      (cisPts queries)[i]? = (cisPts queries)[i']? → i = i' := by
    intro i hi i' hi' hii
    rw [hidxSet, List.mem_filter, List.mem_range] at hi hi'
    rw [List.getElem?_eq_getElem hi.1, List.getElem?_eq_getElem hi'.1] at hii
    have hnodup : (cisPts queries).Nodup :=
      nodup_dedup_foldl queries (·.point) [] List.nodup_nil
    have h2 : (⟨i, hi.1⟩ : Fin (cisPts queries).length) = ⟨i', hi'.1⟩ :=
      List.nodup_iff_injective_getElem.mp hnodup (Option.some.inj hii)
    exact congrArg Fin.val h2
  -- the recorded evaluation at `q.point`'s index is `q`'s own claimed evaluation
  have hgj : ((qs.find? (fun q' => decide (cisPIdx queries q'.point = j))).map (·.eval))
      = some q.eval := by
    rcases hfind : qs.find? (fun q' => decide (cisPIdx queries q'.point = j)) with _ | q'
    · have : (qs.find? (fun q' => decide (cisPIdx queries q'.point = j))).isSome := by
        rw [List.find?_isSome]
        exact ⟨q, hqmem, by simp [hj]⟩
      rw [hfind] at this
      exact absurd this (by simp)
    · rw [hfind]
      have hpred := List.find?_some hfind
      rw [decide_eq_true_eq] at hpred
      have hmem' := List.mem_of_find?_eq_some hfind
      have hq'q : q' ∈ queries := (List.mem_filter.mp hmem').1
      have hq'id : q'.commId = q.commId := by
        have := (List.mem_filter.mp hmem').2
        rw [decide_eq_true_eq] at this
        exact this.trans hek
      have hq'pt : q'.point = q.point := by
        have h1 : (cisPts queries)[cisPIdx queries q'.point]? = some q'.point :=
          getElem?_findIdx_self (mem_dedup_foldl queries (·.point) [] hq'q)
        rw [hpred, hjget] at h1
        exact (Option.some.inj h1).symm
      simp only [Option.map_some, Option.some.injEq]
      exact hdet q' hq'q hq'id hq'pt
  -- route the entry to its point set
  have hslmem : idxSet ∈ cisSetList queries := by
    have h1 := mem_dedup_foldl (cisData queries) (fun x => x.2.2.1) [] hcd
    simpa using h1
  have hsilt : (cisSetList queries).findIdx (fun x => decide (x = idxSet))
      < (cisSetList queries).length :=
    List.findIdx_lt_length_of_exists ⟨idxSet, hslmem, by simp⟩
  have hsiget : (cisSetList queries)[(cisSetList queries).findIdx
      (fun x => decide (x = idxSet))]? = some idxSet :=
    getElem?_findIdx_self hslmem
  set si := (cisSetList queries).findIdx (fun x => decide (x = idxSet)) with hsi
  have hrouted : (e.1, e.2, idxSet, evals) ∈ cisRouted queries si := by
    rw [cisRouted]
    refine List.mem_filter.mpr ⟨List.mem_reverse.mpr hcd, ?_⟩
    simp [hsi]
  set m := (cisRouted queries si).findIdx
    (fun x => decide (x = (e.1, e.2, idxSet, evals))) with hmdef
  have hm : m < (cisRouted queries si).length := by
    rw [hmdef]
    exact List.findIdx_lt_length_of_exists
      ⟨(e.1, e.2, idxSet, evals), hrouted, by simp⟩
  have hrm : (cisRouted queries si)[m] = (e.1, e.2, idxSet, evals) := by
    have hget := getElem?_findIdx_self hrouted
    rw [List.getElem?_eq_getElem hm] at hget
    exact Option.some.inj (by simpa [hmdef] using hget)
  -- the set's point list is the everywhere-defined extraction over the index set
  have hpts : ((cisSetList queries).map fun s => s.filterMap
      fun i => (cisPts queries)[i]?).getD si [] = idxSet.filterMap fun i => (cisPts queries)[i]? := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hsiget]
    simp
  refine ⟨si, ?_, m, ?_, ?_, ?_, ?_, ?_⟩
  · show si < ((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).length
    rw [List.length_map, List.length_range]
    exact hsilt
  · show m < (((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).getD si []).length
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [List.length_range]; exact hsilt), List.getElem_range]
    simpa using hm
  · intro c₀
    show (((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map (·.1)).getD si []).getD m c₀ = q.commId
    have hlen1 : si < ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map (·.1)).length := by
      rw [List.length_map, List.length_range]; exact hsilt
    have hin : ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map (·.1)).getD si [] = (cisRouted queries si).map (·.1) := by
      rw [List.getD_eq_getElem _ _ hlen1, List.getElem_map, List.getElem_range]
    rw [hin, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm), List.getElem_map, hrm]
    exact hek
  · intro d₀
    show (((((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).getD si []).getD m d₀).1)
        = q.commitment
    have hlen1 : si < ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).length := by
      rw [List.length_map, List.length_range]; exact hsilt
    rw [List.getD_eq_getElem _ _ hlen1, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm), List.getElem_map, hrm]
    exact hecommit
  · show q.point ∈ ((cisSetList queries).map fun s => s.filterMap
      fun i => (cisPts queries)[i]?).getD si []
    rw [hpts]
    exact List.mem_filterMap.mpr ⟨j, hjmem, hjget⟩
  · intro d₀ z₀
    show (((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).getD si []).getD m d₀
        |>.2.getD ((((cisSetList queries).map fun s => s.filterMap
          fun i => (cisPts queries)[i]?).getD si []).idxOf q.point) z₀
      = q.eval
    have hlen1 : si < ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).length := by
      rw [List.length_map, List.length_range]; exact hsilt
    have hin : ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).getD si []
        = (cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2) := by
      rw [List.getD_eq_getElem _ _ hlen1, List.getElem_map, List.getElem_range]
    have hentry : (((cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2)).getD m d₀)
        = (e.2, evals) := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm), List.getElem_map, hrm]
    rw [hin, hentry, hpts]
    show evals.getD ((idxSet.filterMap fun i => (cisPts queries)[i]?).idxOf q.point) z₀ = q.eval
    rw [filterMap_idxOf_of_forall_isSome idxSet hfsome hfinj hjmem hjget, hevals,
      filterMap_getD_idxOf_of_forall_isSome z₀ idxSet hgsome hjmem hgj]

/-- Computed indices and their routing specification for one commitment slot.  The indices are
ordinary data obtained by searching the verifier's deterministic grouping; only their validity is
proof-valued. -/
structure ConstructIntermediateSetsRoute {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G)) (c : CommitmentId)
    (commitment : CommitmentRef k F G) where
  setIndex : Nat
  setIndex_lt : setIndex < (constructIntermediateSets queries).sets.length
  memberIndex : Nat
  memberIndex_lt :
    memberIndex < ((constructIntermediateSets queries).sets.getD setIndex []).length
  id_eq : ∀ c₀,
    ((constructIntermediateSets queries).ids.getD setIndex []).getD memberIndex c₀ = c
  commitment_eq : ∀ d₀,
    (((constructIntermediateSets queries).sets.getD setIndex []).getD memberIndex d₀).1 = commitment
  all_queries : ∀ q ∈ queries, q.commId = c →
    q.point ∈ (constructIntermediateSets queries).points.getD setIndex [] ∧
    ∀ d₀ (z₀ : F),
      (((constructIntermediateSets queries).sets.getD setIndex []).getD memberIndex d₀).2.getD
        (((constructIntermediateSets queries).points.getD setIndex []).idxOf q.point) z₀ = q.eval

/-- **Computed general slot routing, all queries of one slot.** The slot named by `c` is routed to
a single member of a single point set, and *every* query on that slot lands there. The definition
returns the actual `findIdx` choices as data. -/
def constructIntermediateSets_comm_route {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) {c : CommitmentId}
    {q₀ : VerifierQuery k F G} (hq₀ : q₀ ∈ queries) (hq₀c : q₀.commId = c)
    (hdet : ∀ q ∈ queries, ∀ q' ∈ queries, q.commId = q'.commId → q.point = q'.point →
      q.eval = q'.eval)
    (hcommit : ∀ q ∈ queries, q.commId = c → q.commitment = q₀.commitment) :
    ConstructIntermediateSetsRoute queries c q₀.commitment := by
  let e : CommitmentId × CommitmentRef k F G := (c, q₀.commitment)
  have he : e ∈ cisComms queries := by
    obtain ⟨e', he', hek'⟩ := cisComms_fold_covers queries [] hq₀
    have hecommit' : e'.2 = q₀.commitment := by
      rcases cisComms_fold_prov queries [] he' with h0 | ⟨q, hq, heq⟩
      · exact absurd h0 List.not_mem_nil
      · rw [heq] at hek' ⊢
        exact hcommit q hq (hek'.trans hq₀c)
    have heq : e' = e := by
      apply Prod.ext
      · exact hek'.trans hq₀c
      · exact hecommit'
    rwa [← heq]
  have hek : e.1 = c := rfl
  have hecommit : e.2 = q₀.commitment := rfl
  have hcd : (e.1, e.2,
      (List.range (cisPts queries).length).filter
        (fun i => ((queries.filter (fun q'' => decide (q''.commId = e.1))).map
          (fun q' => cisPIdx queries q'.point)).contains i),
      ((List.range (cisPts queries).length).filter
        (fun i => ((queries.filter (fun q'' => decide (q''.commId = e.1))).map
          (fun q' => cisPIdx queries q'.point)).contains i)).filterMap
        (fun i => ((queries.filter (fun q'' => decide (q''.commId = e.1))).find?
          (fun q' => decide (cisPIdx queries q'.point = i))).map (·.eval)))
      ∈ cisData queries :=
    List.mem_map.mpr ⟨e, he, rfl⟩
  set qs := queries.filter (fun q'' => decide (q''.commId = e.1)) with hqs
  set idxSet := (List.range (cisPts queries).length).filter
    (fun i => (qs.map (fun q' => cisPIdx queries q'.point)).contains i) with hidxSet
  set evals := idxSet.filterMap
    (fun i => (qs.find? (fun q' => decide (cisPIdx queries q'.point = i))).map (·.eval))
    with hevals
  -- both extractions are everywhere defined on the index set, and the point one is injective
  have hfsome : ∀ i ∈ idxSet, ((cisPts queries)[i]?).isSome := by
    intro i hi
    rw [hidxSet, List.mem_filter, List.mem_range] at hi
    rw [List.getElem?_eq_getElem hi.1]
    exact Option.isSome_some
  have hgsome : ∀ i ∈ idxSet,
      ((qs.find? (fun q' => decide (cisPIdx queries q'.point = i))).map (·.eval)).isSome := by
    intro i hi
    rw [hidxSet, List.mem_filter] at hi
    have hxq := (List.contains_iff_mem).mp hi.2
    obtain ⟨q', hq', hq'i⟩ := List.mem_map.mp hxq
    have hfind : (qs.find? (fun q'' => decide (cisPIdx queries q''.point = i))).isSome := by
      rw [List.find?_isSome]
      exact ⟨q', hq', by simp [hq'i]⟩
    simpa using hfind
  have hfinj : ∀ i ∈ idxSet, ∀ i' ∈ idxSet,
      (cisPts queries)[i]? = (cisPts queries)[i']? → i = i' := by
    intro i hi i' hi' hii
    rw [hidxSet, List.mem_filter, List.mem_range] at hi hi'
    rw [List.getElem?_eq_getElem hi.1, List.getElem?_eq_getElem hi'.1] at hii
    have hnodup : (cisPts queries).Nodup :=
      nodup_dedup_foldl queries (·.point) [] List.nodup_nil
    have h2 : (⟨i, hi.1⟩ : Fin (cisPts queries).length) = ⟨i', hi'.1⟩ :=
      List.nodup_iff_injective_getElem.mp hnodup (Option.some.inj hii)
    exact congrArg Fin.val h2
  -- route the entry to its point set
  have hslmem : idxSet ∈ cisSetList queries := by
    have h1 := mem_dedup_foldl (cisData queries) (fun x => x.2.2.1) [] hcd
    simpa using h1
  have hsilt : (cisSetList queries).findIdx (fun x => decide (x = idxSet))
      < (cisSetList queries).length :=
    List.findIdx_lt_length_of_exists ⟨idxSet, hslmem, by simp⟩
  have hsiget : (cisSetList queries)[(cisSetList queries).findIdx
      (fun x => decide (x = idxSet))]? = some idxSet :=
    getElem?_findIdx_self hslmem
  set si := (cisSetList queries).findIdx (fun x => decide (x = idxSet)) with hsi
  have hrouted : (e.1, e.2, idxSet, evals) ∈ cisRouted queries si := by
    rw [cisRouted]
    refine List.mem_filter.mpr ⟨List.mem_reverse.mpr hcd, ?_⟩
    simp [hsi]
  set m := (cisRouted queries si).findIdx
    (fun x => decide (x = (e.1, e.2, idxSet, evals))) with hmdef
  have hm : m < (cisRouted queries si).length := by
    rw [hmdef]
    exact List.findIdx_lt_length_of_exists
      ⟨(e.1, e.2, idxSet, evals), hrouted, by simp⟩
  have hrm : (cisRouted queries si)[m] = (e.1, e.2, idxSet, evals) := by
    have hget := getElem?_findIdx_self hrouted
    rw [List.getElem?_eq_getElem hm] at hget
    exact Option.some.inj (by simpa [hmdef] using hget)
  have hpts : ((cisSetList queries).map fun s => s.filterMap
      fun i => (cisPts queries)[i]?).getD si [] = idxSet.filterMap fun i => (cisPts queries)[i]? := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hsiget]
    simp
  have hlen1 : si < ((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).length := by
    rw [List.length_map, List.length_range]; exact hsilt
  have hin : ((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).getD si []
      = (cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2) := by
    rw [List.getD_eq_getElem _ _ hlen1, List.getElem_map, List.getElem_range]
  refine
    { setIndex := si
      setIndex_lt := ?_
      memberIndex := m
      memberIndex_lt := ?_
      id_eq := ?_
      commitment_eq := ?_
      all_queries := ?_ }
  · show si < ((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).length
    exact hlen1
  · show m < (((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).getD si []).length
    rw [hin, List.length_map]
    exact hm
  · intro c₀
    show (((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map (·.1)).getD si []).getD m c₀ = c
    have hlen1' : si < ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map (·.1)).length := by
      rw [List.length_map, List.length_range]; exact hsilt
    have hin' : ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map (·.1)).getD si [] = (cisRouted queries si).map (·.1) := by
      rw [List.getD_eq_getElem _ _ hlen1', List.getElem_map, List.getElem_range]
    rw [hin', List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm), List.getElem_map,
      hrm]
  · intro d₀
    show (((((List.range (cisSetList queries).length).map fun si' =>
      (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).getD si []).getD m d₀).1)
        = q₀.commitment
    rw [hin, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm), List.getElem_map,
      hrm]
  · intro q hq hqc
    have hqmem : q ∈ qs :=
      List.mem_filter.mpr ⟨hq, by rw [decide_eq_true_eq]; exact hqc.trans hek.symm⟩
    have hjlt : cisPIdx queries q.point < (cisPts queries).length :=
      List.findIdx_lt_length_of_exists
        ⟨q.point, mem_dedup_foldl queries (·.point) [] hq, by simp⟩
    have hjget : (cisPts queries)[cisPIdx queries q.point]? = some q.point :=
      getElem?_findIdx_self (mem_dedup_foldl queries (·.point) [] hq)
    have hjmem : cisPIdx queries q.point ∈ idxSet := by
      rw [hidxSet]
      refine List.mem_filter.mpr ⟨List.mem_range.mpr hjlt, ?_⟩
      exact (List.contains_iff_mem).mpr (List.mem_map.mpr ⟨q, hqmem, rfl⟩)
    have hgj : ((qs.find? (fun q' =>
        decide (cisPIdx queries q'.point = cisPIdx queries q.point))).map (·.eval))
        = some q.eval := by
      rcases hfind : qs.find? (fun q' =>
          decide (cisPIdx queries q'.point = cisPIdx queries q.point)) with _ | q'
      · have : (qs.find? (fun q' =>
            decide (cisPIdx queries q'.point = cisPIdx queries q.point))).isSome := by
          rw [List.find?_isSome]
          exact ⟨q, hqmem, by simp⟩
        rw [hfind] at this
        exact absurd this (by simp)
      · rw [hfind]
        have hpred := List.find?_some hfind
        rw [decide_eq_true_eq] at hpred
        have hmem' := List.mem_of_find?_eq_some hfind
        have hq'q : q' ∈ queries := (List.mem_filter.mp hmem').1
        have hq'id : q'.commId = q.commId := by
          have := (List.mem_filter.mp hmem').2
          rw [decide_eq_true_eq] at this
          rw [this, hek, hqc]
        have hq'pt : q'.point = q.point := by
          have h1 : (cisPts queries)[cisPIdx queries q'.point]? = some q'.point :=
            getElem?_findIdx_self (mem_dedup_foldl queries (·.point) [] hq'q)
          rw [hpred, hjget] at h1
          exact (Option.some.inj h1).symm
        simp only [Option.map_some, Option.some.injEq]
        exact hdet q' hq'q q hq hq'id hq'pt
    constructor
    · show q.point ∈ ((cisSetList queries).map fun s => s.filterMap
        fun i => (cisPts queries)[i]?).getD si []
      rw [hpts]
      exact List.mem_filterMap.mpr ⟨cisPIdx queries q.point, hjmem, hjget⟩
    · intro d₀ z₀
      show (((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).getD si []).getD m d₀
          |>.2.getD ((((cisSetList queries).map fun s => s.filterMap
            fun i => (cisPts queries)[i]?).getD si []).idxOf q.point) z₀
        = q.eval
      have hentry : (((cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2)).getD m d₀)
          = (e.2, evals) := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm), List.getElem_map,
          hrm]
      rw [hin, hentry, hpts]
      show evals.getD ((idxSet.filterMap fun i => (cisPts queries)[i]?).idxOf q.point) z₀
        = q.eval
      rw [filterMap_idxOf_of_forall_isSome idxSet hfsome hfinj hjmem hjget, hevals,
        filterMap_getD_idxOf_of_forall_isSome z₀ idxSet hgsome hjmem hgj]

/-- Proposition-valued compatibility wrapper for the computed route. -/
theorem constructIntermediateSets_comm_routed_all {k : ℕ} {F G : Type*} [DecidableEq F]
    [DecidableEq G] (queries : List (VerifierQuery k F G)) {c : CommitmentId}
    {q₀ : VerifierQuery k F G} (hq₀ : q₀ ∈ queries) (hq₀c : q₀.commId = c)
    (hdet : ∀ q ∈ queries, ∀ q' ∈ queries, q.commId = q'.commId → q.point = q'.point →
      q.eval = q'.eval)
    (hcommit : ∀ q ∈ queries, q.commId = c → q.commitment = q₀.commitment) :
    ∃ i, i < (constructIntermediateSets queries).sets.length ∧
      ∃ m, m < ((constructIntermediateSets queries).sets.getD i []).length ∧
        (∀ c₀, ((constructIntermediateSets queries).ids.getD i []).getD m c₀ = c) ∧
        (∀ d₀, (((constructIntermediateSets queries).sets.getD i []).getD m d₀).1
          = q₀.commitment) ∧
        ∀ q ∈ queries, q.commId = c →
          q.point ∈ (constructIntermediateSets queries).points.getD i [] ∧
          ∀ d₀ (z₀ : F),
            (((constructIntermediateSets queries).sets.getD i []).getD m d₀).2.getD
              (((constructIntermediateSets queries).points.getD i []).idxOf q.point) z₀
            = q.eval := by
  let route := constructIntermediateSets_comm_route queries hq₀ hq₀c hdet hcommit
  exact ⟨route.setIndex, route.setIndex_lt, route.memberIndex, route.memberIndex_lt,
    route.id_eq, route.commitment_eq, route.all_queries⟩

/-- Under canonical slot resolution, each grouped member carries the commitment named by its ID. -/
theorem constructIntermediateSets_member_commitment_eq_of_id
    {k : ℕ} {F G : Type*} [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G))
    (resolve : CommitmentId -> CommitmentRef k F G)
    (hcanonical : ∀ q ∈ queries, q.commitment = resolve q.commId)
    (i m : Nat) (hm : m < ((constructIntermediateSets queries).sets.getD i []).length)
    {c : CommitmentId} (c0 : CommitmentId)
    (hid : ((constructIntermediateSets queries).ids.getD i []).getD m c0 = c)
    (d0 : CommitmentRef k F G × List F) :
    (((constructIntermediateSets queries).sets.getD i []).getD m d0).1 = resolve c := by
  classical
  have hi : i < (constructIntermediateSets queries).sets.length := by
    by_contra h
    rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)] at hm
    simp at hm
  change i < ((List.range (cisSetList queries).length).map fun si =>
    (cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2)).length at hi
  change m < (((List.range (cisSetList queries).length).map fun si =>
    (cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2)).getD i []).length at hm
  change (((List.range (cisSetList queries).length).map fun si =>
    (cisRouted queries si).map (·.1)).getD i []).getD m c0 = c at hid
  change (((((List.range (cisSetList queries).length).map fun si =>
    (cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2)).getD i []).getD m d0).1)
      = resolve c
  have hi' : i < (cisSetList queries).length := by
    simpa using hi
  have hsets : ((List.range (cisSetList queries).length).map fun si =>
      (cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2)).getD i [] =
      (cisRouted queries i).map fun cd => (cd.2.1, cd.2.2.2) := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi'),
      List.getElem_map, List.getElem_range]
  have hids : ((List.range (cisSetList queries).length).map fun si =>
      (cisRouted queries si).map (·.1)).getD i [] =
      (cisRouted queries i).map (·.1) := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi'),
      List.getElem_map, List.getElem_range]
  rw [hsets] at hm ⊢
  rw [hids] at hid
  have hm' : m < (cisRouted queries i).length := by simpa using hm
  let cd := (cisRouted queries i)[m]'hm'
  have hcdRouted : cd ∈ cisRouted queries i := List.getElem_mem hm'
  have hcdData : cd ∈ cisData queries := by
    exact List.mem_reverse.mp (List.mem_filter.mp hcdRouted).1
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hcdData
  have heprov := cisComms_fold_prov queries [] he
  rcases heprov with h0 | ⟨q, hq, hqe⟩
  · exact absurd h0 List.not_mem_nil
  · have hcdId : cd.1 = q.commId := by
      have h := congrArg (fun x => x.1) heq.symm
      simpa [hqe] using h
    have hcdCommitment : cd.2.1 = q.commitment := by
      have h := congrArg (fun x => x.2.1) heq.symm
      simpa [hqe] using h
    have hid' : cd.1 = c := by
      have := hid
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm'),
        List.getElem_map] at this
      exact this
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hm'),
      List.getElem_map]
    change cd.2.1 = resolve c
    exact hcdCommitment.trans ((hcanonical q hq).trans
      (congrArg resolve (hcdId.symm.trans hid')))

/-! ### Per-class query membership, with the claimed evaluation

The per-class query-membership lemmas locate a class's queries
by slot and point. The feed bindings also need the third component — each query's claimed
evaluation is the proof string's own claim — so the lemmas below restate membership for every
class with the evaluation included: the column families, the permutation products at their three
rotations, the five lookup openings, and the common permutation columns. -/

/-- Every aligned layout and evaluation entry appears as its corresponding column query. -/
theorem columnQueries_layout_mem_eval {k' : ℕ} {F G' : Type*} [Field F] (omega x : F)
    (commitment : ℕ → G') (mkId : ℕ → CommitmentId) (layout : List (ℕ × ℤ)) (evals : List F)
    {j : ℕ} (hjl : j < layout.length) (hje : j < evals.length) :
    ∃ q ∈ columnQueries (k := k') omega x commitment mkId layout evals,
      q.commId = mkId (layout.getD j (0, 0)).1 ∧
      q.point = rotateOmega omega x (layout.getD j (0, 0)).2 ∧
      q.eval = evals.getD j 0 := by
  have hzip : j < (layout.zip evals).length := by
    rw [List.length_zip]; omega
  refine ⟨_, List.mem_map.mpr ⟨(layout.zip evals)[j], List.getElem_mem hzip, rfl⟩, ?_, ?_, ?_⟩
  · show mkId ((layout.zip evals)[j]).1.1 = _
    rw [List.getElem_zip, List.getD_eq_getElem _ _ hjl]
  · show rotateOmega omega x ((layout.zip evals)[j]).1.2 = _
    rw [List.getElem_zip, List.getD_eq_getElem _ _ hjl]
  · show ((layout.zip evals)[j]).2 = _
    rw [List.getElem_zip, List.getD_eq_getElem _ _ hje]

/-- Each in-range fixed layout entry contributes a deployed opening query: slot `fixedCol`, the
rotated point, and the proof string's claimed fixed evaluation. -/
theorem fixed_query_mem_assembleQueries {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G) (ch : Challenges shape.k F)
    {j : ℕ} (hjl : j < vk.fixedQueryLayout.length) (hje : j < shape.numFixedQueries) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.fixedCol (vk.fixedQueryLayout.getD j (0, 0)).1 ∧
      q.point = rotateOmega vk.omega ch.x (vk.fixedQueryLayout.getD j (0, 0)).2 ∧
      q.eval = finFn ps.fixedEvals j := by
  obtain ⟨q, hqmem, hqid, hqpt, hqev⟩ := columnQueries_layout_mem_eval (k' := shape.k) vk.omega
    ch.x vk.fixedCommitment CommitmentId.fixedCol vk.fixedQueryLayout (List.ofFn ps.fixedEvals)
    hjl (by rw [List.length_ofFn]; exact hje)
  refine ⟨q, ?_, hqid, hqpt, ?_⟩
  · simp only [assembleQueries]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inr hqmem)))))
  · rw [hqev, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hje), List.getElem_ofFn,
      finFn, dif_pos hje]

/-- Advice-query membership in `assembleQueries`, with the claimed evaluation. -/
theorem advice_query_mem_assembleQueries_eval {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (pi : Fin shape.numProofs)
    {j : ℕ} (hjl : j < vk.adviceQueryLayout.length) (hje : j < shape.numAdviceQueries) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.adviceCol pi (vk.adviceQueryLayout.getD j (0, 0)).1 ∧
      q.point = rotateOmega vk.omega ch.x (vk.adviceQueryLayout.getD j (0, 0)).2 ∧
      q.eval = finFn (ps.adviceEvals pi) j := by
  obtain ⟨q, hqmem, hqid, hqpt, hqev⟩ := columnQueries_layout_mem_eval (k' := shape.k) vk.omega
    ch.x (finFnG (ps.adviceCommitments pi)) (CommitmentId.adviceCol pi) vk.adviceQueryLayout
    (List.ofFn (ps.adviceEvals pi)) hjl (by rw [List.length_ofFn]; exact hje)
  refine ⟨q, ?_, hqid, hqpt, ?_⟩
  · simp only [assembleQueries]
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl ?_)))))
    refine List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨pi, rfl⟩, ?_⟩
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inr hqmem)))))
  · rw [hqev, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hje), List.getElem_ofFn,
      finFn, dif_pos hje]

/-- Instance-query membership in `assembleQueries`, with the claimed evaluation. -/
theorem instance_query_mem_assembleQueries_eval {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (pi : Fin shape.numProofs)
    {j : ℕ} (hjl : j < vk.instanceQueryLayout.length) (hje : j < shape.numInstanceQueries) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.instanceCol pi (vk.instanceQueryLayout.getD j (0, 0)).1 ∧
      q.point = rotateOmega vk.omega ch.x (vk.instanceQueryLayout.getD j (0, 0)).2 ∧
      q.eval = finFn (ps.instanceEvals pi) j := by
  obtain ⟨q, hqmem, hqid, hqpt, hqev⟩ := columnQueries_layout_mem_eval (k' := shape.k) vk.omega
    ch.x (instanceCommitment pi) (CommitmentId.instanceCol pi) vk.instanceQueryLayout
    (List.ofFn (ps.instanceEvals pi)) hjl (by rw [List.length_ofFn]; exact hje)
  refine ⟨q, ?_, hqid, hqpt, ?_⟩
  · simp only [assembleQueries]
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl ?_)))))
    refine List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨pi, rfl⟩, ?_⟩
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl hqmem)))))
  · rw [hqev, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hje), List.getElem_ofFn,
      finFn, dif_pos hje]

/-- A per-proof builder's query is an `assembleQueries` query: the permutation section of
sub-proof `pi`. -/
private theorem mem_assembleQueries_of_mem_perm {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (pi : Fin shape.numProofs) {q : VerifierQuery shape.k F G}
    (hq : q ∈ permutationQueries ch.x (rotateOmega vk.omega ch.x 1)
      (rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1)))
      (CommitmentId.permProduct pi)
      (List.ofFn (fun s => (ps.permutationProduct pi s, ps.permutationSetEvals pi s)))) :
    q ∈ assembleQueries vk instanceCommitment ps ch := by
  simp only [assembleQueries]
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inl ?_)))))
  refine List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨pi, rfl⟩, ?_⟩
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hq)))

/-- The lookup section of sub-proof `pi`, as `mem_assembleQueries_of_mem_perm`. -/
private theorem mem_assembleQueries_of_mem_lookup {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (pi : Fin shape.numProofs) {q : VerifierQuery shape.k F G}
    (hq : q ∈ lookupQueries ch.x (rotateOmega vk.omega ch.x (-1)) (rotateOmega vk.omega ch.x 1)
      (CommitmentId.lookupProduct pi) (CommitmentId.lookupPermInput pi)
      (CommitmentId.lookupPermTable pi)
      (List.ofFn (fun l => (LookupCommitments.mk (ps.lookupProduct pi l) (ps.lookupPermutedInput pi l)
        (ps.lookupPermutedTable pi l), ps.lookupEvals pi l)))) :
    q ∈ assembleQueries vk instanceCommitment ps ch := by
  simp only [assembleQueries]
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inl ?_)))))
  refine List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨pi, rfl⟩, ?_⟩
  exact List.mem_append.mpr (Or.inr hq)

/-- The permutation product of set `s` is opened at `ch.x` claiming its `eval`. -/
theorem perm_product_query_mem_assembleQueries {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (pi : Fin shape.numProofs)
    (s : Fin shape.numPermutationSets) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.permProduct pi s ∧ q.point = ch.x ∧
      q.eval = (ps.permutationSetEvals pi s).eval := by
  set sets := List.ofFn (fun s => (ps.permutationProduct pi s, ps.permutationSetEvals pi s))
    with hsets
  have hslt : (s : ℕ) < (sets.zip (List.range sets.length)).length := by
    rw [List.length_zip, List.length_range, min_self, hsets, List.length_ofFn]
    exact s.isLt
  refine ⟨{ point := ch.x,
            commitment := .point ((sets.zip (List.range sets.length))[(s : ℕ)]).1.1,
            eval := ((sets.zip (List.range sets.length))[(s : ℕ)]).1.2.eval,
            commId := CommitmentId.permProduct pi ((sets.zip (List.range sets.length))[(s : ℕ)]).2 },
    mem_assembleQueries_of_mem_perm vk instanceCommitment ps ch pi ?_, ?_, rfl, ?_⟩
  · rw [permutationQueries]
    refine List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
      ⟨(sets.zip (List.range sets.length))[(s : ℕ)], List.getElem_mem hslt,
        List.mem_cons_self ..⟩))
  · show CommitmentId.permProduct pi ((sets.zip (List.range sets.length))[(s : ℕ)]).2 = _
    rw [List.getElem_zip, List.getElem_range]
  · show ((sets.zip (List.range sets.length))[(s : ℕ)]).1.2.eval = _
    simp [List.getElem_zip, hsets, List.getElem_ofFn]

/-- The permutation product of set `s` is opened at `ω · ch.x` claiming its `nextEval`. -/
theorem perm_product_next_query_mem_assembleQueries {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (pi : Fin shape.numProofs)
    (s : Fin shape.numPermutationSets) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.permProduct pi s ∧ q.point = rotateOmega vk.omega ch.x 1 ∧
      q.eval = (ps.permutationSetEvals pi s).nextEval := by
  set sets := List.ofFn (fun s => (ps.permutationProduct pi s, ps.permutationSetEvals pi s))
    with hsets
  have hslt : (s : ℕ) < (sets.zip (List.range sets.length)).length := by
    rw [List.length_zip, List.length_range, min_self, hsets, List.length_ofFn]
    exact s.isLt
  refine ⟨{ point := rotateOmega vk.omega ch.x 1,
            commitment := .point ((sets.zip (List.range sets.length))[(s : ℕ)]).1.1,
            eval := ((sets.zip (List.range sets.length))[(s : ℕ)]).1.2.nextEval,
            commId := CommitmentId.permProduct pi ((sets.zip (List.range sets.length))[(s : ℕ)]).2 },
    mem_assembleQueries_of_mem_perm vk instanceCommitment ps ch pi ?_, ?_, rfl, ?_⟩
  · rw [permutationQueries]
    refine List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
      ⟨(sets.zip (List.range sets.length))[(s : ℕ)], List.getElem_mem hslt, ?_⟩))
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · show CommitmentId.permProduct pi ((sets.zip (List.range sets.length))[(s : ℕ)]).2 = _
    rw [List.getElem_zip, List.getElem_range]
  · show ((sets.zip (List.range sets.length))[(s : ℕ)]).1.2.nextEval = _
    simp [List.getElem_zip, hsets, List.getElem_ofFn]

/-- For every set except the last whose `lastEval` is claimed, the permutation product is also
opened at `ω^{-(blind+1)} · ch.x` claiming that value (halo2's `rev().skip(1)` walk). -/
theorem perm_product_last_query_mem_assembleQueries {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (pi : Fin shape.numProofs)
    (s : Fin shape.numPermutationSets) (hlast : (s : ℕ) + 1 < shape.numPermutationSets)
    {le : F} (hle : (ps.permutationSetEvals pi s).lastEval = some le) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.permProduct pi s ∧
      q.point = rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1)) ∧
      q.eval = le := by
  set sets := List.ofFn (fun s => (ps.permutationProduct pi s, ps.permutationSetEvals pi s))
    with hsets
  set indexed := sets.zip (List.range sets.length) with hindexed
  have hilen : indexed.length = shape.numPermutationSets := by
    rw [hindexed, List.length_zip, List.length_range, min_self, hsets, List.length_ofFn]
  have hslt : (s : ℕ) < indexed.length := by rw [hilen]; exact s.isLt
  have hpos : shape.numPermutationSets - 2 - (s : ℕ) < (indexed.reverse.drop 1).length := by
    rw [List.length_drop, List.length_reverse, hilen]
    omega
  have hrd : (indexed.reverse.drop 1)[shape.numPermutationSets - 2 - (s : ℕ)]'hpos
      = indexed[(s : ℕ)]'hslt := by
    rw [List.getElem_drop, List.getElem_reverse]
    congr 1
    rw [hilen]
    omega
  have hE2 : (indexed[(s : ℕ)]'hslt).1.2 = ps.permutationSetEvals pi s := by
    simp [hindexed, hsets, List.getElem_zip, List.getElem_ofFn]
  have hE2' : (indexed[(s : ℕ)]'hslt).2 = (s : ℕ) := by
    simp [hindexed, List.getElem_zip, List.getElem_range]
  refine ⟨{ point := rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1)),
            commitment := .point (indexed[(s : ℕ)]'hslt).1.1,
            eval := le,
            commId := CommitmentId.permProduct pi (indexed[(s : ℕ)]'hslt).2 }, ?_, ?_, rfl, rfl⟩
  · apply mem_assembleQueries_of_mem_perm vk instanceCommitment ps ch pi
    rw [permutationQueries]
    refine List.mem_append.mpr (Or.inr (List.mem_filterMap.mpr
      ⟨indexed[(s : ℕ)]'hslt, hrd ▸ List.getElem_mem hpos, ?_⟩))
    rw [hE2, hle, Option.map_some]
  · show CommitmentId.permProduct pi (indexed[(s : ℕ)]'hslt).2 = _
    rw [hE2']

/-- The lookup product of lookup `l` is opened at `ch.x` claiming its `productEval`. -/
theorem lookup_product_query_mem_assembleQueries {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (pi : Fin shape.numProofs) (l : Fin shape.numLookups) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.lookupProduct pi l ∧ q.point = ch.x ∧
      q.eval = (ps.lookupEvals pi l).productEval := by
  set lks := List.ofFn (fun l => (LookupCommitments.mk (ps.lookupProduct pi l) (ps.lookupPermutedInput pi l)
    (ps.lookupPermutedTable pi l),
    ps.lookupEvals pi l)) with hlks
  have hllt : (l : ℕ) < (lks.zip (List.range lks.length)).length := by
    rw [List.length_zip, List.length_range, min_self, hlks, List.length_ofFn]
    exact l.isLt
  refine ⟨{ point := ch.x,
            commitment := .point ((lks.zip (List.range lks.length))[(l : ℕ)]).1.1.product,
            eval := ((lks.zip (List.range lks.length))[(l : ℕ)]).1.2.productEval,
            commId := CommitmentId.lookupProduct pi ((lks.zip (List.range lks.length))[(l : ℕ)]).2 },
    mem_assembleQueries_of_mem_lookup vk instanceCommitment ps ch pi ?_, ?_, rfl, ?_⟩
  · rw [lookupQueries]
    exact List.mem_flatMap.mpr ⟨(lks.zip (List.range lks.length))[(l : ℕ)],
      List.getElem_mem hllt, List.mem_cons_self ..⟩
  · show CommitmentId.lookupProduct pi ((lks.zip (List.range lks.length))[(l : ℕ)]).2 = _
    rw [List.getElem_zip, List.getElem_range]
  · show ((lks.zip (List.range lks.length))[(l : ℕ)]).1.2.productEval = _
    simp [List.getElem_zip, hlks, List.getElem_ofFn]

/-- The lookup product of lookup `l` is opened at `ω · ch.x` claiming its `productNextEval`. -/
theorem lookup_product_next_query_mem_assembleQueries {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (pi : Fin shape.numProofs) (l : Fin shape.numLookups) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.lookupProduct pi l ∧ q.point = rotateOmega vk.omega ch.x 1 ∧
      q.eval = (ps.lookupEvals pi l).productNextEval := by
  set lks := List.ofFn (fun l => (LookupCommitments.mk (ps.lookupProduct pi l) (ps.lookupPermutedInput pi l)
    (ps.lookupPermutedTable pi l),
    ps.lookupEvals pi l)) with hlks
  have hllt : (l : ℕ) < (lks.zip (List.range lks.length)).length := by
    rw [List.length_zip, List.length_range, min_self, hlks, List.length_ofFn]
    exact l.isLt
  refine ⟨{ point := rotateOmega vk.omega ch.x 1,
            commitment := .point ((lks.zip (List.range lks.length))[(l : ℕ)]).1.1.product,
            eval := ((lks.zip (List.range lks.length))[(l : ℕ)]).1.2.productNextEval,
            commId := CommitmentId.lookupProduct pi ((lks.zip (List.range lks.length))[(l : ℕ)]).2 },
    mem_assembleQueries_of_mem_lookup vk instanceCommitment ps ch pi ?_, ?_, rfl, ?_⟩
  · rw [lookupQueries]
    refine List.mem_flatMap.mpr ⟨(lks.zip (List.range lks.length))[(l : ℕ)],
      List.getElem_mem hllt, ?_⟩
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  · show CommitmentId.lookupProduct pi ((lks.zip (List.range lks.length))[(l : ℕ)]).2 = _
    rw [List.getElem_zip, List.getElem_range]
  · show ((lks.zip (List.range lks.length))[(l : ℕ)]).1.2.productNextEval = _
    simp [List.getElem_zip, hlks, List.getElem_ofFn]

/-- The permuted input of lookup `l` is opened at `ch.x` claiming its `permutedInputEval`. -/
theorem lookup_permInput_query_mem_assembleQueries {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (pi : Fin shape.numProofs) (l : Fin shape.numLookups) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.lookupPermInput pi l ∧ q.point = ch.x ∧
      q.eval = (ps.lookupEvals pi l).permutedInputEval := by
  set lks := List.ofFn (fun l => (LookupCommitments.mk (ps.lookupProduct pi l) (ps.lookupPermutedInput pi l)
    (ps.lookupPermutedTable pi l),
    ps.lookupEvals pi l)) with hlks
  have hllt : (l : ℕ) < (lks.zip (List.range lks.length)).length := by
    rw [List.length_zip, List.length_range, min_self, hlks, List.length_ofFn]
    exact l.isLt
  refine ⟨{ point := ch.x,
            commitment := .point ((lks.zip (List.range lks.length))[(l : ℕ)]).1.1.permutedInput,
            eval := ((lks.zip (List.range lks.length))[(l : ℕ)]).1.2.permutedInputEval,
            commId := CommitmentId.lookupPermInput pi ((lks.zip (List.range lks.length))[(l : ℕ)]).2 },
    mem_assembleQueries_of_mem_lookup vk instanceCommitment ps ch pi ?_, ?_, rfl, ?_⟩
  · rw [lookupQueries]
    refine List.mem_flatMap.mpr ⟨(lks.zip (List.range lks.length))[(l : ℕ)],
      List.getElem_mem hllt, ?_⟩
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · show CommitmentId.lookupPermInput pi ((lks.zip (List.range lks.length))[(l : ℕ)]).2 = _
    rw [List.getElem_zip, List.getElem_range]
  · show ((lks.zip (List.range lks.length))[(l : ℕ)]).1.2.permutedInputEval = _
    simp [List.getElem_zip, hlks, List.getElem_ofFn]

/-- The permuted input of lookup `l` is opened at `ω⁻¹ · ch.x` claiming its
`permutedInputInvEval`. -/
theorem lookup_permInput_inv_query_mem_assembleQueries {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (pi : Fin shape.numProofs) (l : Fin shape.numLookups) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.lookupPermInput pi l ∧ q.point = rotateOmega vk.omega ch.x (-1) ∧
      q.eval = (ps.lookupEvals pi l).permutedInputInvEval := by
  set lks := List.ofFn (fun l => (LookupCommitments.mk (ps.lookupProduct pi l) (ps.lookupPermutedInput pi l)
    (ps.lookupPermutedTable pi l),
    ps.lookupEvals pi l)) with hlks
  have hllt : (l : ℕ) < (lks.zip (List.range lks.length)).length := by
    rw [List.length_zip, List.length_range, min_self, hlks, List.length_ofFn]
    exact l.isLt
  refine ⟨{ point := rotateOmega vk.omega ch.x (-1),
            commitment := .point ((lks.zip (List.range lks.length))[(l : ℕ)]).1.1.permutedInput,
            eval := ((lks.zip (List.range lks.length))[(l : ℕ)]).1.2.permutedInputInvEval,
            commId := CommitmentId.lookupPermInput pi ((lks.zip (List.range lks.length))[(l : ℕ)]).2 },
    mem_assembleQueries_of_mem_lookup vk instanceCommitment ps ch pi ?_, ?_, rfl, ?_⟩
  · rw [lookupQueries]
    refine List.mem_flatMap.mpr ⟨(lks.zip (List.range lks.length))[(l : ℕ)],
      List.getElem_mem hllt, ?_⟩
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))
  · show CommitmentId.lookupPermInput pi ((lks.zip (List.range lks.length))[(l : ℕ)]).2 = _
    rw [List.getElem_zip, List.getElem_range]
  · show ((lks.zip (List.range lks.length))[(l : ℕ)]).1.2.permutedInputInvEval = _
    simp [List.getElem_zip, hlks, List.getElem_ofFn]

/-- The permuted table of lookup `l` is opened at `ch.x` claiming its `permutedTableEval`. -/
theorem lookup_permTable_query_mem_assembleQueries {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (pi : Fin shape.numProofs) (l : Fin shape.numLookups) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.lookupPermTable pi l ∧ q.point = ch.x ∧
      q.eval = (ps.lookupEvals pi l).permutedTableEval := by
  set lks := List.ofFn (fun l => (LookupCommitments.mk (ps.lookupProduct pi l) (ps.lookupPermutedInput pi l)
    (ps.lookupPermutedTable pi l),
    ps.lookupEvals pi l)) with hlks
  have hllt : (l : ℕ) < (lks.zip (List.range lks.length)).length := by
    rw [List.length_zip, List.length_range, min_self, hlks, List.length_ofFn]
    exact l.isLt
  refine ⟨{ point := ch.x,
            commitment := .point ((lks.zip (List.range lks.length))[(l : ℕ)]).1.1.permutedTable,
            eval := ((lks.zip (List.range lks.length))[(l : ℕ)]).1.2.permutedTableEval,
            commId := CommitmentId.lookupPermTable pi ((lks.zip (List.range lks.length))[(l : ℕ)]).2 },
    mem_assembleQueries_of_mem_lookup vk instanceCommitment ps ch pi ?_, ?_, rfl, ?_⟩
  · rw [lookupQueries]
    refine List.mem_flatMap.mpr ⟨(lks.zip (List.range lks.length))[(l : ℕ)],
      List.getElem_mem hllt, ?_⟩
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · show CommitmentId.lookupPermTable pi ((lks.zip (List.range lks.length))[(l : ℕ)]).2 = _
    rw [List.getElem_zip, List.getElem_range]
  · show ((lks.zip (List.range lks.length))[(l : ℕ)]).1.2.permutedTableEval = _
    simp [List.getElem_zip, hlks, List.getElem_ofFn]

/-- The common permutation column `c` is opened at `ch.x` claiming its common evaluation. -/
theorem permCommon_query_mem_assembleQueries {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (c : Fin shape.numPermutationColumns) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = CommitmentId.permCommon c ∧ q.point = ch.x ∧
      q.eval = ps.permutationCommonEvals c := by
  set ces := List.ofFn (fun c => (vk.permutationCommonCommitment c, ps.permutationCommonEvals c))
    with hces
  have hclt : (c : ℕ) < (ces.zip (List.range ces.length)).length := by
    rw [List.length_zip, List.length_range, min_self, hces, List.length_ofFn]
    exact c.isLt
  refine ⟨{ point := ch.x,
            commitment := .point ((ces.zip (List.range ces.length))[(c : ℕ)]).1.1,
            eval := ((ces.zip (List.range ces.length))[(c : ℕ)]).1.2,
            commId := CommitmentId.permCommon ((ces.zip (List.range ces.length))[(c : ℕ)]).2 },
    ?_, ?_, rfl, ?_⟩
  · show _ ∈ assembleQueries vk instanceCommitment ps ch
    simp only [assembleQueries]
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
    rw [permutationCommonQueries]
    exact List.mem_map.mpr ⟨(ces.zip (List.range ces.length))[(c : ℕ)],
      List.getElem_mem hclt, rfl⟩
  · show CommitmentId.permCommon ((ces.zip (List.range ces.length))[(c : ℕ)]).2 = _
    rw [List.getElem_zip, List.getElem_range]
  · show ((ces.zip (List.range ces.length))[(c : ℕ)]).1.2 = _
    simp [List.getElem_zip, hces, List.getElem_ofFn]

/-! ### Vanishing-slot uniqueness

Every builder tags its queries with its own `CommitmentId` constructor family; only
`vanishingQueries` emits the `vanishingH` slot, and it does so exactly once. So the vanishing-`h`
query is the unique carrier of its slot in `assembleQueries` — the uniqueness
`constructIntermediateSets_unique_comm_routed` needs to route it unambiguously. -/

/-- Without duplicate slot-point pairs, equal slots and points identify the same query. -/
theorem eq_of_not_hasDuplicateCommitmentPoint {k : ℕ} {F G : Type*} [DecidableEq F] :
    ∀ {qs : List (VerifierQuery k F G)}, hasDuplicateCommitmentPoint qs = false →
      ∀ {q}, q ∈ qs → ∀ {q'}, q' ∈ qs → q'.commId = q.commId → q'.point = q.point → q' = q := by
  intro qs
  induction qs with
  | nil => intro _ q hq; exact absurd hq List.not_mem_nil
  | cons a t ih =>
      intro hdup q hq q' hq' hid hpt
      rw [hasDuplicateCommitmentPoint, Bool.or_eq_false_iff] at hdup
      obtain ⟨hany, hrec⟩ := hdup
      simp only [List.any_eq_false, decide_eq_true_eq] at hany
      rcases List.mem_cons.mp hq with rfl | hqt
      · rcases List.mem_cons.mp hq' with rfl | hq't
        · rfl
        · exact absurd ⟨hid, hpt⟩ (hany q' hq't)
      · rcases List.mem_cons.mp hq' with rfl | hq't
        · exact absurd ⟨hid.symm, hpt.symm⟩ (hany q hqt)
        · exact ih hrec hqt hq't hid hpt

end Zcash.Snark
