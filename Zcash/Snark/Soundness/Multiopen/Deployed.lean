import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Multiopen.Decode
import Zcash.Snark.Soundness.Multiopen.Compat

/-!
# The deployed multiopen statement is a flat power batch in the `x₄` collapse

`Soundness.Multiopen.Decode` consumes batched openings in flat power form — `P = Σⱼ ξʲ • Cⱼ` and
`v = Σⱼ ξʲ • eⱼ` at distinct `ξ` — which the flat-batch family carries as the assumptions
`hP`/`hv`. This module discharges them: as a function of the `x₄` squeeze the pinned
`deployedCommitment` and `multiopenValue` *are* flat power batches
(`deployedCommitment_x4_batch`, `multiopenValue_x4_batch`), with coefficients read off the
fingerprinted `constructIntermediateSets` grouping.

Power `ξ^j` below the pair count carries an `x₁`-compressed aggregate `qᵢ` and its claimed set
evaluation `uᵢ`, in *reverse* processing order: the collapse folds `acc ↦ ξ·acc + next`, so the
last set processed carries `ξ⁰`. The top power carries the prover's quotient commitment `q′` and
the recomputed `deployedBaseEval`.

So the decode consumes the deployed grouping itself, leaving no separate "flat model = deployed"
obligation at the `x₄` level. The batch columns here are the multiopen aggregates, not circuit
columns; unbatching within a point set is the `x₁` layer, one level down. This module supplies
only deterministic verifier algebra — no accept-measure or rewind-extraction API.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.eval_appendTerm Msm.zero)

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

/-- Reassemble a top power plus a range power sum as one `Fin`-indexed power sum, the last index
carrying the top term — the flat power-batch shape consumed by the opened AGM decoder. -/
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
(`x4BatchCommitments`); the represented `x₁` coordinates un-batch each aggregate into its member
commitments. -/
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
def deployedX4Qs [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : List (Msm shape.k Fp G) :=
  let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)
  ((grouped.sets.zip grouped.points).map (fun sp => compressSet ch.x1 sp.1 sp.2.length)).map Prod.fst

/-- The deployed `x₄`-collapse pair list: the point-set aggregates zipped with the prover's claimed set
evaluations `u`, in the order the collapse folds them. -/
def deployedX4Pairs [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : List (Msm shape.k Fp G × Fp) :=
  (deployedX4Qs vk instanceCommitment ps ch).zip (List.ofFn ps.multiopenU)

/-- The number of `x₄`-collapsed `(qᵢ, uᵢ)` pairs. The `x₄` batch has this many aggregate columns plus
the `q′` slot. -/
def deployedX4PairCount [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : ℕ :=
  (deployedX4Pairs vk instanceCommitment ps ch).length

/-- The deployed base evaluation `msm_eval` the `x₄` collapse starts from: the `x₂`-combined,
vanishing-divided Lagrange step (`multiopenEval`) over the fingerprinted grouping — the value the
quotient commitment `q′` is claimed to open to. -/
def deployedBaseEval [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : Fp :=
  let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)
  let compressed := (grouped.sets.zip grouped.points).map (fun sp => compressSet ch.x1 sp.1 sp.2.length)
  multiopenEval ch.x2 ch.x3
    (((grouped.points.zip (compressed.map Prod.snd)).zip (List.ofFn ps.multiopenU)).map
      (fun p => (p.1.1, p.1.2, p.2)))

/-- The deployed `x₄` batch column commitments: ascending `ξ`-powers carry the point-set aggregates in
reverse fold order, the top power the quotient commitment `q′`. These are the "columns" the `x₄`-level
decode recovers — the fingerprinted grouping's own aggregates, not a modeled flat batch. -/
def x4BatchCommitments [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1) → G :=
  fun j =>
    if (j : ℕ) < deployedX4PairCount vk instanceCommitment ps ch then
      ((deployedX4Pairs vk instanceCommitment ps ch).reverse.getD (j : ℕ) (Msm.zero shape.k Fp G, 0)).1.eval
        ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩
    else ps.multiopenQPrime

/-- The deployed `x₄` batch column evaluations: ascending `ξ`-powers carry the claimed set evaluations
`uᵢ` in reverse fold order, the top power the recomputed base evaluation `msm_eval`. -/
def x4BatchEvals [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    Fin (deployedX4PairCount vk instanceCommitment ps ch + 1) → Fp :=
  fun j =>
    if (j : ℕ) < deployedX4PairCount vk instanceCommitment ps ch then
      ((deployedX4Pairs vk instanceCommitment ps ch).reverse.getD (j : ℕ) (Msm.zero shape.k Fp G, 0)).2
    else deployedBaseEval vk instanceCommitment ps ch

/-- **The deployed commitment is a flat power batch in the `x₄` squeeze.** For every `ξ`, replacing
only the `x₄` field in the challenge record leaves the upstream query assembly, grouping, `x₁`
compression, and base evaluation fixed. The resulting `deployedCommitment` is therefore the
`ξ`-power combination of the deployed aggregates. -/
theorem deployedCommitment_x4_batch [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (ξ : Fp) :
    deployedCommitment urs hk vk instanceCommitment ps {ch with x4 := ξ}
      = ∑ j : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1),
          ξ ^ (j : ℕ) • x4BatchCommitments urs hk vk instanceCommitment ps ch j := by
  show (assembleOpening ch.x1 ch.x2 ch.x3 ξ ps.multiopenQPrime (List.ofFn ps.multiopenU)
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) (Msm.zero shape.k Fp G)).1.eval
        ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ = _
  rw [assembleOpening, multiopenCombine_fst_eval_powerForm, powerSum_ite_last]
  rfl

omit [AddCommGroup G] [Module Fp G] in
/-- **The deployed value is a flat power batch in the `x₄` squeeze.** The value companion of
`deployedCommitment_x4_batch`: over `{ch with x4 := ξ}`, the pinned `multiopenValue` is the `ξ`-power
combination of the claimed set evaluations with the base evaluation on top — the discharge of
the flat-batch model boundary's `hv`. -/
theorem multiopenValue_x4_batch [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (ξ : Fp) :
    multiopenValue vk instanceCommitment ps {ch with x4 := ξ}
      = ∑ j : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1), ξ ^ (j : ℕ) • x4BatchEvals vk instanceCommitment ps ch j := by
  show (assembleOpening ch.x1 ch.x2 ch.x3 ξ ps.multiopenQPrime (List.ofFn ps.multiopenU)
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) (Msm.zero shape.k Fp G)).2 = _
  rw [assembleOpening, multiopenCombine_snd_powerForm, powerSum_ite_last]
  rfl

/-- The queries the fingerprinted grouping routes to point set `i`, in the accumulate order the `x₁`
compression folds them (`MultiopenGrouped.sets`, zipped with the set's points). -/
def deployedSetQueries [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (i : ℕ) :
    List (CommitmentRef shape.k Fp G × List Fp) :=
  (let grouped := constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)
   (grouped.sets.zip grouped.points).getD i ([], [])).1

/-- The slot identities of point set `i`'s routed members, positionally aligned with
`deployedSetQueries` (halo2 `CommitmentData` retains its commitment identity through the grouping;
`constructIntermediateSets_sets_ids_aligned`). `deployedSetCommIds vk instanceCommitment ps ch i |>.getD m` names
*which* commitment — advice/instance/fixed column, permutation/lookup product, vanishing — member
`(i, m)` is, tying the decoded member polynomials back to the verifying key's query layout. -/
def deployedSetCommIds [DecidableEq G] [Inhabited G] {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (i : ℕ) : List CommitmentId :=
  (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).ids.getD i []

omit [AddCommGroup G] [Module Fp G] in
/-- The commitment-identifier list of a deployed point set has one entry per member query.
Restored after the upstream multiopen prune: the canonical resolver bounds member indices with
it, and no replacement was carried over. -/
theorem deployedSetCommIds_length [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (i : ℕ) :
    (deployedSetCommIds vk instanceCommitment ps ch i).length
      = (deployedSetQueries vk instanceCommitment ps ch i).length := by
  simp only [deployedSetCommIds, deployedSetQueries]
  rw [constructIntermediateSets_zip_sets_getD]
  exact constructIntermediateSets_sets_ids_aligned (assembleQueries vk instanceCommitment ps ch) i


/-- **The two-level batch structure, made explicit.** The `x₄`-level batch column `i` (a point-set
aggregate of `deployedX4Qs`) is itself a flat power batch in the `x₁` squeeze of the member commitments
the fingerprinted grouping routes to that set. Composing with `deployedCommitment_x4_batch`: the deployed
commitment is the `x₄`-power batch of `x₁`-power batches of the actual query commitments — the deployed
two-level collapse in closed form. -/
theorem deployedX4Qs_getD_eval [DecidableEq G] [Inhabited G] {shape : Shape}
    (g : Fin (2 ^ shape.k) → G) (w u : G) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {i : ℕ}
    (hi : i < (deployedX4Qs vk instanceCommitment ps ch).length) :
    ((deployedX4Qs vk instanceCommitment ps ch).getD i (Msm.zero shape.k Fp G)).eval ⟨shape.k, g, w, u⟩
      = ∑ j ∈ Finset.range (deployedSetQueries vk instanceCommitment ps ch i).length,
          ch.x1 ^ j • ((deployedSetQueries vk instanceCommitment ps ch i).getD j (.point 0, [])).1.eval
            ⟨shape.k, g, w, u⟩ := by
  have hzip : i < ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.zip
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points).length := by
    simpa [deployedX4Qs] using hi
  have hq : (deployedX4Qs vk instanceCommitment ps ch).getD i (Msm.zero shape.k Fp G)
      = (compressSet ch.x1 (deployedSetQueries vk instanceCommitment ps ch i)
          (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.zip
            (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points).getD i
              ([], [])).2.length).1 := by
    rw [deployedX4Qs, List.getD_eq_getElem _ _ (by simpa [deployedX4Qs] using hi),
      List.getElem_map, List.getElem_map, deployedSetQueries,
      List.getD_eq_getElem _ _ hzip]
  rw [hq, compressSet_fst_eval]

/-! ## From the `x₄` batch positions back to the sets, and the member binding -/

/-- The in-range `x₄` batch columns, set-indexed: batch column `j` is the aggregate of point set
`count − 1 − j` (the collapse folds the sets so the last one processed carries `ξ⁰`). -/
theorem x4BatchCommitments_getD [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {j : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1)}
    (hj : (j : ℕ) < deployedX4PairCount vk instanceCommitment ps ch) :
    x4BatchCommitments urs hk vk instanceCommitment ps ch j
      = ((deployedX4Qs vk instanceCommitment ps ch).getD (deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ))
            (Msm.zero shape.k Fp G)).eval ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
  rw [x4BatchCommitments, if_pos hj]
  have hj₁ : (j : ℕ) < (deployedX4Pairs vk instanceCommitment ps ch).reverse.length := by
    rw [List.length_reverse]
    exact hj
  have hj₂ : deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ) < (deployedX4Pairs vk instanceCommitment ps ch).length := by
    have hj' : (j : ℕ) < (deployedX4Pairs vk instanceCommitment ps ch).length := hj
    simp only [deployedX4PairCount]
    omega
  have hj₃ : deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ) < (deployedX4Qs vk instanceCommitment ps ch).length := by
    have hle : (deployedX4Pairs vk instanceCommitment ps ch).length ≤ (deployedX4Qs vk instanceCommitment ps ch).length := by
      simp only [deployedX4Pairs, List.length_zip]
      exact min_le_left _ _
    simp only [deployedX4PairCount]
    omega
  rw [List.getD_eq_getElem _ _ hj₁, List.getElem_reverse, List.getD_eq_getElem _ _ hj₃]
  congr 1
  exact congrArg Prod.fst List.getElem_zip

omit [AddCommGroup G] [Module Fp G] in
/-- The `x₄` pair count is the length of the pair list — the definitional unfolding, as a lemma so
downstream files can use it without delta-reducing the sealed definition. -/
theorem deployedX4PairCount_eq [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    deployedX4PairCount vk instanceCommitment ps ch = (deployedX4Pairs vk instanceCommitment ps ch).length := rfl

omit [AddCommGroup G] [Module Fp G] in
/-- The top slot of the `x₄` batch evaluations is the recomputed base evaluation: the slot index
equals the pair count, so the branch that reads a point set is not taken. -/
theorem x4BatchEvals_top [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    x4BatchEvals vk instanceCommitment ps ch ⟨deployedX4PairCount vk instanceCommitment ps ch, Nat.lt_succ_self _⟩
      = deployedBaseEval vk instanceCommitment ps ch := by
  show (if deployedX4PairCount vk instanceCommitment ps ch < deployedX4PairCount vk instanceCommitment ps ch then _
    else deployedBaseEval vk instanceCommitment ps ch) = deployedBaseEval vk instanceCommitment ps ch
  rw [if_neg (lt_irrefl _)]




end Deployed

end Zcash.Snark
