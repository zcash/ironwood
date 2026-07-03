import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.ForkingProbability

/-!
# The deployed multiopen statement is a flat power batch in the `x₄` collapse

The decoded-column layer (`Soundness.MultiopenDecode`) consumes batched openings in flat power form —
`P = Σⱼ ξʲ • Cⱼ` and `v = Σⱼ ξʲ • eⱼ` at distinct batching challenges `ξ` — and until now that form was a
*model boundary*: `acceptedBatchFamily_of_rewinds` carried the power shape of the deployed statement as
the assumptions `hP`/`hv`. This module discharges them against the deployed verifier. As a function of the
`x₄` squeeze — over the runs `{ch with x4 := ξ}`, which `Soundness.Forking.reprogramX4` identifies with
oracle reprogramming — the pinned `deployedCommitment`/`multiopenValue` *are* flat power batches
(`deployedCommitment_x4_batch`/`multiopenValue_x4_batch`), and the coefficient families are read off the
fingerprinted `constructIntermediateSets` grouping (`x4BatchCommitments`/`x4BatchEvals`):

* power `ξ^j` for `j <` the pair count carries an `x₁`-compressed point-set aggregate `qᵢ` and its claimed
  set evaluation `uᵢ` — in *reverse* processing order, because the deployed collapse folds
  `acc ↦ ξ·acc + next` so the last set processed carries `ξ⁰`;
* the top power carries the prover's quotient commitment `q′` and the recomputed base evaluation
  `msm_eval` (`deployedBaseEval`).

So the batch the decode consumes is the deployed grouping itself — per the issue-#21 principle the decode
*consumes* the fingerprint-validated `constructIntermediateSets` output rather than re-modeling the
batching as an independent flat power series; no separate "flat model = deployed" obligation is left at
the `x₄` level. The batch "columns" at this level are the multiopen aggregates (`qᵢ`, `q′`), not the
circuit columns: unbatching *within* a point set is the `x₁` layer, one level down
(`x1_batch_open_soundV`).

Downstream, `deployedMultiopenRewind_of_x4Rewinds` instantiates `acceptedBatchFamily_of_rewinds` with
`hP`/`hv` *proven*: an injective family of accepting rewound runs over `{ch with x4 := ξᵣ}` (containing
the honest run) yields the terminal `MultiopenRewindForRelation` for the pinned deployed statement over
the deployed aggregates. `deployedMultiopenRewind_of_x4Prob` derives that family from an accept-*measure*
hypothesis via the single-squeeze counting form of the forking floor
(`exists_injective_accepting_of_measure`, `Soundness.ForkingProbability`) — the multiopen instance of the
codebase-wide rewinding-extraction floor, carrying the same random-oracle uniformity axiom as every
`hprob` (`Soundness.RandomOracle`).

-/

namespace Zcash.Snark

/-! ## The scale-and-add fold in closed power form -/

section PowerFold

variable {F : Type*} [Field F] {M : Type*} [AddCommMonoid M] [Module F M]

/-- Closed form of the collapse fold `acc ↦ ξ • acc + g p`: the initial value climbs to the top power
and the folded entries carry ascending powers in *reverse* order (the last entry folded is multiplied by
`ξ⁰`). Stated over an arbitrary entry projection `g` and an arbitrary `getD` default `d` (never evaluated
in range), so the multiopen collapse's commitment and value components both instantiate it directly. -/
theorem foldl_smul_add_powerForm {α : Type*} (ξ : F) (g : α → M) (d : α) (l : List α) (a₀ : M) :
    l.foldl (fun acc p => ξ • acc + g p) a₀
      = ξ ^ l.length • a₀
        + ∑ j ∈ Finset.range l.length, ξ ^ j • g (l.reverse.getD j d) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l m ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, List.length_append,
        List.reverse_append]
      simp only [List.length_cons, List.length_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_smul]
      rw [smul_add, smul_smul, ← pow_succ', Finset.smul_sum]
      have hpow : ∀ j, ξ • ξ ^ j • g (l.reverse.getD j d) = ξ ^ (j + 1) • g (l.reverse.getD j d) := by
        intro j
        rw [smul_smul, ← pow_succ']
      rw [Finset.sum_congr rfl fun j _ => hpow j]
      abel

/-- Reassemble a top power plus a range power sum as one `Fin`-indexed power sum, the last index carrying
the top term — the summation shape `BatchOpeningsForWitness` consumes. -/
theorem powerSum_ite_last (ξ : F) (n : ℕ) (c : ℕ → M) (a₀ : M) :
    ξ ^ n • a₀ + ∑ j ∈ Finset.range n, ξ ^ j • c j
      = ∑ j : Fin (n + 1), ξ ^ (j : ℕ) • (if (j : ℕ) < n then c j else a₀) := by
  rw [Fin.sum_univ_castSucc]
  have hcast : ∀ j : Fin n,
      ξ ^ ((j.castSucc : Fin (n + 1)) : ℕ)
          • (if ((j.castSucc : Fin (n + 1)) : ℕ) < n then c ((j.castSucc : Fin (n + 1)) : ℕ) else a₀)
        = ξ ^ (j : ℕ) • c (j : ℕ) := by
    intro j
    rw [Fin.val_castSucc, if_pos j.is_lt]
  rw [Finset.sum_congr rfl fun j _ => hcast j,
    Fin.sum_univ_eq_sum_range (fun j => ξ ^ j • c j) n, Fin.val_last, if_neg (lt_irrefl n)]
  exact add_comm _ _

end PowerFold

/-- A pair-valued fold whose components do not interact is the pair of the component folds. The multiopen
`x₄` collapse (`multiopenCombine`) has exactly this shape: the MSM component folds the compressed set
commitments, the value component the claimed set evaluations. -/
theorem foldl_prod_componentwise {α β γ δ : Type*} (l : List (α × β))
    (f : γ → α → γ) (g : δ → β → δ) (c₀ : γ) (d₀ : δ) :
    l.foldl (fun st p => (f st.1 p.1, g st.2 p.2)) (c₀, d₀)
      = (l.foldl (fun c p => f c p.1) c₀, l.foldl (fun d p => g d p.2) d₀) := by
  induction l generalizing c₀ d₀ with
  | nil => rfl
  | cons p l ih => exact ih (f c₀ p.1) (g d₀ p.2)

/-- The multiopen `x₄` collapse as the pair of its component folds: the MSM side scale-and-adds the
compressed set commitments into the appended `q′`, the value side the claimed set evaluations into the
base evaluation. -/
theorem multiopenCombine_eq_pair {k : ℕ} {F G : Type*} [Field F] (x4 : F) (qPrime : G)
    (qs : List (Msm k F G)) (u : List F) (e₀ : F) (incoming : Msm k F G) :
    multiopenCombine x4 qPrime qs u e₀ incoming
      = ((qs.zip u).foldl (fun c p => (c.scale x4).add p.1) (incoming.appendTerm 1 qPrime),
         (qs.zip u).foldl (fun d p => d * x4 + p.2) e₀) := by
  rw [multiopenCombine]
  exact foldl_prod_componentwise (qs.zip u) (fun c a => (c.scale x4).add a)
    (fun d b => d * x4 + b) (incoming.appendTerm 1 qPrime) e₀

/-- Evaluating the MSM component's scale-and-add fold is the scale-and-add fold of the evaluations
(`Msm.eval_scale`/`eval_add` pushed through the fold). -/
theorem Msm.eval_foldl_scale_add {F G : Type*} [Field F] [AddCommGroup G] [Module F G] {β : Type*}
    (urs : URS G) (ξ : F) (l : List (Msm urs.k F G × β)) (m₀ : Msm urs.k F G) :
    (l.foldl (fun acc p => (acc.scale ξ).add p.1) m₀).eval urs
      = l.foldl (fun acc p => ξ • acc + p.1.eval urs) (m₀.eval urs) := by
  induction l generalizing m₀ with
  | nil => rfl
  | cons p l ih =>
      rw [List.foldl_cons, ih, List.foldl_cons, Msm.eval_add, Msm.eval_scale]

/-! ## The `x₄` collapse in power form (generic multiopen level) -/

section CombinePowerForm

variable {k : ℕ} {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The MSM component of the multiopen `x₄` collapse over the zero incoming accumulator, evaluated, in
power form: the quotient commitment `q′` at the top power, the zipped `(qᵢ, uᵢ)` pairs' commitment
evaluations at ascending powers in reverse fold order. -/
theorem multiopenCombine_fst_eval_powerForm (urs : URS G) (ξ : F) (qPrime : G)
    (qs : List (Msm urs.k F G)) (u : List F) (e₀ : F) :
    (multiopenCombine ξ qPrime qs u e₀ (Msm.zero urs.k F G)).1.eval urs
      = ξ ^ (qs.zip u).length • qPrime
        + ∑ j ∈ Finset.range (qs.zip u).length,
            ξ ^ j • ((qs.zip u).reverse.getD j (Msm.zero urs.k F G, 0)).1.eval urs := by
  rw [multiopenCombine_eq_pair]
  show ((qs.zip u).foldl (fun c p => (c.scale ξ).add p.1)
      ((Msm.zero urs.k F G).appendTerm 1 qPrime)).eval urs = _
  rw [Msm.eval_foldl_scale_add,
    foldl_smul_add_powerForm ξ (fun p => p.1.eval urs) (Msm.zero urs.k F G, 0) (qs.zip u)
      (((Msm.zero urs.k F G).appendTerm 1 qPrime).eval urs),
    Msm.eval_appendTerm, Msm.eval_zero, one_smul, zero_add]

omit [AddCommGroup G] [Module F G] in
/-- The value component of the multiopen `x₄` collapse, in power form: the base evaluation `msm_eval` at
the top power, the zipped pairs' claimed set evaluations at ascending powers in reverse fold order. -/
theorem multiopenCombine_snd_powerForm (ξ : F) (qPrime : G)
    (qs : List (Msm k F G)) (u : List F) (e₀ : F) (incoming : Msm k F G) :
    (multiopenCombine ξ qPrime qs u e₀ incoming).2
      = ξ ^ (qs.zip u).length • e₀
        + ∑ j ∈ Finset.range (qs.zip u).length,
            ξ ^ j • ((qs.zip u).reverse.getD j (Msm.zero k F G, 0)).2 := by
  rw [multiopenCombine_eq_pair]
  show (qs.zip u).foldl (fun d p => d * ξ + p.2) e₀ = _
  have hfun : (fun (d : F) (p : Msm k F G × F) => d * ξ + p.2)
      = fun d p => ξ • d + p.2 := by
    funext d p
    rw [smul_eq_mul, mul_comm]
  rw [hfun,
    foldl_smul_add_powerForm ξ (fun p : Msm k F G × F => p.2) (Msm.zero k F G, 0) (qs.zip u) e₀]

end CombinePowerForm

/-! ## The `x₁` within-set layer: each aggregate is a power batch of its member commitments -/

section X1PowerForm

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Accumulating one query commitment into a point set's compressed MSM adds its power-weighted group
value — uniformly over the plain-point and MSM commitment-reference cases. -/
theorem accumulateCommitment_eval (urs : URS G) (pow : F) (c : CommitmentRef urs.k F G)
    (acc : Msm urs.k F G) :
    (accumulateCommitment pow c acc).eval urs = acc.eval urs + pow • c.eval urs := by
  cases c with
  | point p => rw [accumulateCommitment, CommitmentRef.eval, Msm.eval_appendTerm]
  | msm m => rw [accumulateCommitment, CommitmentRef.eval, Msm.eval_add, Msm.eval_scale]

/-- The `x₁` compression fold, evaluated, over a general accumulator: each remaining query contributes
its commitment's group value at the running power. -/
theorem compressSet_fold_eval (urs : URS G) (x1 : F)
    (sq : List (CommitmentRef urs.k F G × List F)) (m₀ : Msm urs.k F G) (ev₀ : List F) (p₀ : F) :
    ((sq.foldl (fun (st : Msm urs.k F G × List F × F) qc =>
        (accumulateCommitment st.2.2 qc.1 st.1,
         (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
         st.2.2 * x1)) (m₀, ev₀, p₀)).1).eval urs
      = m₀.eval urs
        + ∑ j ∈ Finset.range sq.length,
            (p₀ * x1 ^ j) • (sq.getD j (.point 0, [])).1.eval urs := by
  induction sq generalizing m₀ ev₀ p₀ with
  | nil => simp
  | cons qc sq ih =>
      rw [List.foldl_cons]
      dsimp only
      rw [ih, accumulateCommitment_eval, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
      have hpow : ∀ j ∈ Finset.range sq.length,
          (p₀ * x1 * x1 ^ j) • (sq.getD j (.point 0, [])).1.eval urs
            = (p₀ * x1 ^ (j + 1)) • (sq.getD j (.point 0, [])).1.eval urs := by
        intro j _
        rw [mul_assoc, ← pow_succ']
      rw [Finset.sum_congr rfl hpow]
      abel

/-- **The within-set aggregate is a flat power batch in `x₁`.** The compressed point-set commitment
evaluates to the `x₁`-power combination of its member commitments' group values, in processing order —
the `x₁` half of the two-level un-batching. At the `x₄` level the decoded columns are these aggregates
(`x4BatchCommitments`), and rewinding the `x₁` squeeze un-batches them into the member commitments
(`x1_batch_open_soundV`; the values are heterogeneous across `x₁` runs because `x₃` re-randomizes). -/
theorem compressSet_fst_eval (urs : URS G) (x1 : F)
    (sq : List (CommitmentRef urs.k F G × List F)) (np : ℕ) :
    (compressSet x1 sq np).1.eval urs
      = ∑ j ∈ Finset.range sq.length, x1 ^ j • (sq.getD j (.point 0, [])).1.eval urs := by
  simp only [compressSet]
  rw [compressSet_fold_eval, Msm.eval_zero, zero_add]
  exact Finset.sum_congr rfl fun j _ => by rw [one_mul]

end X1PowerForm

/-! ## The deployed `x₄` batch families, read off the fingerprinted grouping -/

section Deployed

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The deployed `x₁`-compressed point-set aggregates, exactly as `assembleOpening` builds them from the
fingerprinted `constructIntermediateSets` grouping: per point set (in processing order), the `x₁`-power
fold of the commitments routed to it. -/
def deployedX4Qs [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : List (Msm shape.k Fp G) :=
  let grouped := constructIntermediateSets (assembleQueries vk ps ch)
  ((grouped.sets.zip grouped.points).map (fun sp => compressSet ch.x1 sp.1 sp.2.length)).map Prod.fst

/-- The deployed `x₄`-collapse pair list: the point-set aggregates zipped with the prover's claimed set
evaluations `u`, in the order the collapse folds them. -/
def deployedX4Pairs [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : List (Msm shape.k Fp G × Fp) :=
  (deployedX4Qs vk ps ch).zip (List.ofFn ps.multiopenU)

/-- The number of `x₄`-collapsed `(qᵢ, uᵢ)` pairs. The `x₄` batch has this many aggregate columns plus
the `q′` slot. -/
def deployedX4PairCount [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : ℕ :=
  (deployedX4Pairs vk ps ch).length

/-- The deployed base evaluation `msm_eval` the `x₄` collapse starts from: the `x₂`-combined,
vanishing-divided Lagrange step (`multiopenEval`) over the fingerprinted grouping — the value the
quotient commitment `q′` is claimed to open to. -/
def deployedBaseEval [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : Fp :=
  let grouped := constructIntermediateSets (assembleQueries vk ps ch)
  let compressed := (grouped.sets.zip grouped.points).map (fun sp => compressSet ch.x1 sp.1 sp.2.length)
  multiopenEval ch.x2 ch.x3
    (((grouped.points.zip (compressed.map Prod.snd)).zip (List.ofFn ps.multiopenU)).map
      (fun p => (p.1.1, p.1.2, p.2)))

/-- The deployed `x₄` batch column commitments: ascending `ξ`-powers carry the point-set aggregates in
reverse fold order, the top power the quotient commitment `q′`. These are the "columns" the `x₄`-level
decode recovers — the fingerprinted grouping's own aggregates, not a modeled flat batch. -/
noncomputable def x4BatchCommitments [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Fin (deployedX4PairCount vk ps ch + 1) → G :=
  fun j =>
    if (j : ℕ) < deployedX4PairCount vk ps ch then
      ((deployedX4Pairs vk ps ch).reverse.getD (j : ℕ) (Msm.zero shape.k Fp G, 0)).1.eval
        ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩
    else ps.multiopenQPrime

/-- The deployed `x₄` batch column evaluations: ascending `ξ`-powers carry the claimed set evaluations
`uᵢ` in reverse fold order, the top power the recomputed base evaluation `msm_eval`. -/
def x4BatchEvals [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    Fin (deployedX4PairCount vk ps ch + 1) → Fp :=
  fun j =>
    if (j : ℕ) < deployedX4PairCount vk ps ch then
      ((deployedX4Pairs vk ps ch).reverse.getD (j : ℕ) (Msm.zero shape.k Fp G, 0)).2
    else deployedBaseEval vk ps ch

/-- **The deployed commitment is a flat power batch in the `x₄` squeeze.** Over the rewound runs
`{ch with x4 := ξ}` — everything upstream of the collapse (`assembleQueries`, the grouping, the `x₁`
compression, the base evaluation) is untouched by the redraw — the pinned `deployedCommitment` is the
`ξ`-power combination of the deployed aggregates. This discharges `acceptedBatchFamily_of_rewinds`'s
`hP` for the deployed verifier, closing the flat-batch model boundary at the `x₄` level. -/
theorem deployedCommitment_x4_batch [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (ξ : Fp) :
    deployedCommitment urs hk vk ps {ch with x4 := ξ}
      = ∑ j : Fin (deployedX4PairCount vk ps ch + 1),
          ξ ^ (j : ℕ) • x4BatchCommitments urs hk vk ps ch j := by
  show (assembleOpening ch.x1 ch.x2 ch.x3 ξ ps.multiopenQPrime (List.ofFn ps.multiopenU)
      (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).1.eval
        ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ = _
  rw [assembleOpening, multiopenCombine_fst_eval_powerForm, powerSum_ite_last]
  rfl

omit [AddCommGroup G] [Module Fp G] in
/-- **The deployed value is a flat power batch in the `x₄` squeeze.** The value companion of
`deployedCommitment_x4_batch`: over `{ch with x4 := ξ}`, the pinned `multiopenValue` is the `ξ`-power
combination of the claimed set evaluations with the base evaluation on top — the discharge of
`acceptedBatchFamily_of_rewinds`'s `hv`. -/
theorem multiopenValue_x4_batch [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (ξ : Fp) :
    multiopenValue vk ps {ch with x4 := ξ}
      = ∑ j : Fin (deployedX4PairCount vk ps ch + 1), ξ ^ (j : ℕ) • x4BatchEvals vk ps ch j := by
  show (assembleOpening ch.x1 ch.x2 ch.x3 ξ ps.multiopenQPrime (List.ofFn ps.multiopenU)
      (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).2 = _
  rw [assembleOpening, multiopenCombine_snd_powerForm, powerSum_ite_last]
  rfl

/-- The queries the fingerprinted grouping routes to point set `i`, in the accumulate order the `x₁`
compression folds them (`MultiopenGrouped.sets`, zipped with the set's points). -/
def deployedSetQueries [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (i : ℕ) :
    List (CommitmentRef shape.k Fp G × List Fp) :=
  (let grouped := constructIntermediateSets (assembleQueries vk ps ch)
   (grouped.sets.zip grouped.points).getD i ([], [])).1

/-- **The two-level batch structure, made explicit.** The `x₄`-level batch column `i` (a point-set
aggregate of `deployedX4Qs`) is itself a flat power batch in the `x₁` squeeze of the member commitments
the fingerprinted grouping routes to that set. Composing with `deployedCommitment_x4_batch`: the deployed
commitment is the `x₄`-power batch of `x₁`-power batches of the actual query commitments — the deployed
two-level collapse in closed form. -/
theorem deployedX4Qs_getD_eval [DecidableEq G] [Inhabited G] {shape : Shape}
    (g : Fin (2 ^ shape.k) → G) (w u : G) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {i : ℕ}
    (hi : i < (deployedX4Qs vk ps ch).length) :
    ((deployedX4Qs vk ps ch).getD i (Msm.zero shape.k Fp G)).eval ⟨shape.k, g, w, u⟩
      = ∑ j ∈ Finset.range (deployedSetQueries vk ps ch i).length,
          ch.x1 ^ j • ((deployedSetQueries vk ps ch i).getD j (.point 0, [])).1.eval
            ⟨shape.k, g, w, u⟩ := by
  have hzip : i < ((constructIntermediateSets (assembleQueries vk ps ch)).sets.zip
      (constructIntermediateSets (assembleQueries vk ps ch)).points).length := by
    simpa [deployedX4Qs] using hi
  have hq : (deployedX4Qs vk ps ch).getD i (Msm.zero shape.k Fp G)
      = (compressSet ch.x1 (deployedSetQueries vk ps ch i)
          (((constructIntermediateSets (assembleQueries vk ps ch)).sets.zip
            (constructIntermediateSets (assembleQueries vk ps ch)).points).getD i
              ([], [])).2.length).1 := by
    rw [deployedX4Qs, List.getD_eq_getElem _ _ (by simpa [deployedX4Qs] using hi),
      List.getElem_map, List.getElem_map, deployedSetQueries,
      List.getD_eq_getElem _ _ hzip]
  rw [hq, compressSet_fst_eval]

/-- The canonical within-set decode across `x₁` rewinds: the Vandermonde-inverse combination of the
per-run aggregate witnesses — the same explicit combination `decodedColumnFamily_of_batch_openings`
uses at the `x₄` level. Its specification is `x1DecodeCols_commit`/`_reconstruct`/`_value`. -/
noncomputable def x1DecodeCols {m n : ℕ} (z : Fin n → Fp) (a : Fin n → (Fin m → Fp)) :
    Fin n → (Fin m → Fp) :=
  fun j => ∑ r, (Matrix.vandermonde z)⁻¹ j r • a r

/-- The canonical `x₁` decode opens the member commitments: given the per-run commitment equations in
`x₁`-power form at pairwise-distinct compression challenges, column `j` opens `C j`. -/
theorem x1DecodeCols_commit {m n : ℕ} (g : Fin m → G) (C : Fin n → G)
    (z : Fin n → Fp) (hz : Function.Injective z) (a : Fin n → (Fin m → Fp))
    (haC : ∀ r, commitGen g (a r) = ∑ j : Fin n, z r ^ (j : ℕ) • C j) (j : Fin n) :
    commitGen g (x1DecodeCols z a j) = C j :=
  batch_open_with_coeffs g C z a _ (fun i j => by simpa using vandermonde_inv_left z hz i j) haC j

/-- The canonical `x₁` decode reconstructs every run's aggregate witness as its `x₁`-power
combination. -/
theorem x1DecodeCols_reconstruct {m n : ℕ} (z : Fin n → Fp) (hz : Function.Injective z)
    (a : Fin n → (Fin m → Fp)) (r : Fin n) :
    a r = ∑ j : Fin n, z r ^ (j : ℕ) • x1DecodeCols z a j :=
  (batch_open_reconstruct_with_coeffs z a _
    (fun i j => by simpa using vandermonde_inv_right z hz i j) r).symm

/-- The canonical `x₁` decode transports every run's value equation: the run's claimed set evaluation
is the `x₁`-power combination of the decoded columns' values at that run's own evaluation vector
(heterogeneous per run — `x₃` re-randomizes under `x₁` rewinds through the re-sent `q′`). -/
theorem x1DecodeCols_value {m n : ℕ} (z : Fin n → Fp) (hz : Function.Injective z)
    (a : Fin n → (Fin m → Fp)) (b : Fin n → (Fin m → Fp)) (u : Fin n → Fp)
    (hau : ∀ r, commitGen (b r) (a r) = u r) (r : Fin n) :
    ∑ j : Fin n, z r ^ (j : ℕ) • commitGen (b r) (x1DecodeCols z a j) = u r := by
  have hlin : ∑ j : Fin n, z r ^ (j : ℕ) • commitGen (b r) (x1DecodeCols z a j)
      = commitGen (b r) (∑ j : Fin n, z r ^ (j : ℕ) • x1DecodeCols z a j) := by
    rw [commitGen_sum]
    exact Finset.sum_congr rfl fun j _ => (commitGen_smul_left (b r) _ _).symm
  rw [hlin, ← x1DecodeCols_reconstruct z hz a r]
  exact hau r

/-- **Within-set un-batching across `x₁` rewinds (heterogeneous values), existential form.** From
per-run openings of the `x₁`-power aggregates at pairwise-distinct compression challenges — the
commitment equations uniform, the value data heterogeneous, because each run `r` opens at its own
evaluation vector `b r` to its own claimed set evaluation `u r` — the Vandermonde decode recovers
per-column witnesses that (i) open the member commitments, (ii) reconstruct every run's aggregate
witness, and (iii) transport every run's value equation. The `x₁` counterpart of `batch_open_soundV`,
which handles the uniform-`b` case (the `x₄` level, where all rewinds share `x₃`); the canonical
witness is `x1DecodeCols`. -/
theorem x1_batch_open_soundV {m n : ℕ} (g : Fin m → G) (C : Fin n → G)
    (z : Fin n → Fp) (hz : Function.Injective z) (a : Fin n → (Fin m → Fp))
    (b : Fin n → (Fin m → Fp)) (u : Fin n → Fp)
    (haC : ∀ r, commitGen g (a r) = ∑ j : Fin n, z r ^ (j : ℕ) • C j)
    (hau : ∀ r, commitGen (b r) (a r) = u r) :
    ∃ col : Fin n → (Fin m → Fp),
      (∀ j, commitGen g (col j) = C j)
      ∧ (∀ r, a r = ∑ j : Fin n, z r ^ (j : ℕ) • col j)
      ∧ (∀ r, ∑ j : Fin n, z r ^ (j : ℕ) • commitGen (b r) (col j) = u r) :=
  ⟨x1DecodeCols z a, fun j => x1DecodeCols_commit g C z hz a haC j,
    fun r => x1DecodeCols_reconstruct z hz a r, fun r => x1DecodeCols_value z hz a b u hau r⟩

/-- **The deployed `x₄` rewind family, `hP`/`hv` discharged.** From an injective family of accepting
clean IPA transcripts over the rewound runs `{ch with x4 := ξ r}` — with the honest run in the `cur`
slot — the terminal multiopen-rewinding output for the pinned deployed statement, over the deployed
aggregates. This is `acceptedBatchFamily_of_rewinds` with the flat power form now *proven*
(`deployedCommitment_x4_batch`/`multiopenValue_x4_batch`) rather than assumed: no flat-batch scope
hypothesis is left at this level. The runs are the `reprogramX4` reprogramming events
(`Soundness.Forking`); producing them from an accept measure is `deployedMultiopenRewind_of_x4Prob`. -/
noncomputable def deployedMultiopenRewind_of_x4Rewinds [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp}
    (ξ : Fin (deployedX4PairCount vk ps ch + 1) → Fp) (hξinj : Function.Injective ξ)
    (cur : Fin (deployedX4PairCount vk ps ch + 1)) (hcur : ξ cur = ch.x4)
    (htrees : ∀ r, ∃ t : IpaTreeV Fp G urs.k,
      IpaAcceptV urs.g b (deployedCommitment urs hk vk ps {ch with x4 := ξ r})
        (multiopenValue vk ps {ch with x4 := ξ r}) t) :
    MultiopenRewindForRelation urs (deployedCommitment urs hk vk ps ch) b
      (multiopenValue vk ps ch) (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) := by
  have fam := acceptedBatchFamily_of_rewinds (urs := urs) (b := b) ξ hξinj
    (fun x => deployedCommitment urs hk vk ps {ch with x4 := x})
    (fun x => multiopenValue vk ps {ch with x4 := x})
    (fun r => deployedCommitment_x4_batch urs hk vk ps ch (ξ r))
    (fun r => multiopenValue_x4_batch vk ps ch (ξ r))
    cur htrees
  rw [hcur] at fam
  exact multiopenRewindForRelation_of_acceptedFamily fam

/-- **Per-run clean-tree production from the deployed accept, off the relation branch.** If no
nontrivial `(g, U, W)` relation exists, then every accepting `x₄`-rewound run peels through its
`FiatShamirTree` bridge to a clean accepting IPA transcript (`deployed_to_acceptV` cannot land on the
relation branch). This feeds the per-run event of `deployedMultiopenRewind_of_x4Prob` (and its `hcur`,
at `ξ := ch.x4` via structure eta) from `DeployedAccepts`-level facts; a capstone consuming it splits
classically on `HasNontrivialRelation` and short-circuits to the relation disjunct otherwise.

Quantifier-shape caveat: the fixed `ps` here is the constant strategy — its IPA fields open the
honest collapse only — so a `DeployedAccepts` measure over rewound `ξ` runs fed through this lemma
inherits the static dichotomy of the constant rung
(`orchard_verifier_vesta_forking_opening_deployed`). The adaptive analogue would re-send the
post-`x₄` fields (`ipaS` and the IPA opening; note `spliceIpa` splices the rounds but not `ipaS`),
mirroring the `x₁` layer's `spliceMultiopen`. The measure event of
`deployedMultiopenRewind_of_x4Prob` itself — abstract accepting trees for the rewound statements —
carries no such degeneracy. -/
theorem x4_cleanTree_of_deployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w) (ξ : Fp)
    (hFS : FiatShamirTree urs hk vk ps {ch with x4 := ξ} b z blind)
    (hacc : DeployedAccepts urs hk vk ps {ch with x4 := ξ}) :
    ∃ t : IpaTreeV Fp G urs.k,
      IpaAcceptV urs.g b (deployedCommitment urs hk vk ps {ch with x4 := ξ})
        (multiopenValue vk ps {ch with x4 := ξ}) t := by
  obtain ⟨t, ht⟩ := hFS (deployedAccepts_verifierEq urs hk vk ps _ hacc)
  rcases deployed_to_acceptV hz urs.g b (deployedCommitment urs hk vk ps {ch with x4 := ξ})
      (multiopenValue vk ps {ch with x4 := ξ}) blind t ht with hclean | hrel
  · exact ⟨projTree t, hclean⟩
  · exact absurd hrel hnrel

open scoped ENNReal in
open Classical in
/-- **The `x₄` forking floor, multiopen instance.** If the honest run has an accepting clean IPA
transcript and the accept measure of the `x₄`-rewound runs beats `pairCount / p` — the single-squeeze
counting threshold — then the terminal multiopen-rewinding output for the pinned deployed statement
exists over the deployed aggregates. The measure hypothesis carries the same random-oracle uniformity
axiom as every `hprob` (`Soundness.RandomOracle`); the runs are the `reprogramX4` reprogramming events;
each run's accepting transcript is the per-run round-forking output (produced upstream, e.g. by the
`FiatShamirTree` bridges or the round-forking ladder). This is the multiopen instance of the
codebase-wide rewinding-extraction floor — `extractable_of_prob` is the multi-round analogue, and
`exists_injective_accepting_of_measure` (`Soundness.ForkingProbability`) is the counting core. -/
noncomputable def deployedMultiopenRewind_of_x4Prob [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp}
    (hcur : ∃ t : IpaTreeV Fp G urs.k,
      IpaAcceptV urs.g b (deployedCommitment urs hk vk ps ch) (multiopenValue vk ps ch) t)
    (hprob : ((deployedX4PairCount vk ps ch : ℝ≥0∞)) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (fun x =>
          ∃ t : IpaTreeV Fp G urs.k,
            IpaAcceptV urs.g b (deployedCommitment urs hk vk ps {ch with x4 := x})
              (multiopenValue vk ps {ch with x4 := x}) t))) :
    MultiopenRewindForRelation urs (deployedCommitment urs hk vk ps ch) b
      (multiopenValue vk ps ch) (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) := by
  have hx₀ : ∃ t : IpaTreeV Fp G urs.k,
      IpaAcceptV urs.g b (deployedCommitment urs hk vk ps {ch with x4 := ch.x4})
        (multiopenValue vk ps {ch with x4 := ch.x4}) t := hcur
  have hex := exists_injective_accepting_of_measure
    (acc := fun x => ∃ t : IpaTreeV Fp G urs.k,
      IpaAcceptV urs.g b (deployedCommitment urs hk vk ps {ch with x4 := x})
        (multiopenValue vk ps {ch with x4 := x}) t)
    (x₀ := ch.x4) hx₀ hprob
  exact deployedMultiopenRewind_of_x4Rewinds urs hk vk ps ch (Classical.choose hex)
    (Classical.choose_spec hex).1 0 (Classical.choose_spec hex).2.1
    (Classical.choose_spec hex).2.2

end Deployed

end Zcash.Snark
