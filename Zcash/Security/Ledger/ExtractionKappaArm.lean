import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Ledger.ExtractionArm
import Zcash.Security.RedDSA.KnowledgeError
import Zcash.Security.KeyBinding.Probability

/-!
# The extraction-failure arm's κ, discharged in the oracle model

The capstone layer bounds the conservation reduction's extraction-failure arm by the named
knowledge error κ. This module bounds that arm in the challenge-oracle model, at the
reduction's own events: for any `qH`-query-bounded labeled algebraic ledger adversary, the
probability that the output ledger is valid *and* the reduction lands in the arm is at most
`(qH+1)/|F| + (ε_DL + 1/|F|) = (qH+2)/|F| + ε_DL` (from `kappaEvent_measure_le`). As with
the key-binding arm, the bound is joint with validity; the capstones' named κ ranges over an
abstract `PMF (ValidAnnotated …)`, and the experiment-to-`PMF` connection is the
joint-experiment composition (#107).

The sample is a challenge table `O` and the logs `s` of the `m` presented bases. The value
commitment and the binding verification are instantiated at sampled slots, as a record
update of the fixed primitives (`kappaPrimitivesAt`), so the ledger type does not depend on
the sample; the other primitives deliberately stay fixed, and the value and signature fields
are not separated out of `Primitives`. The challenge hash reads the table at
`queryOf R bvk m`, intended to be an injective encoding — collisions only constrain the
algebraic hypotheses, shrinking the covered adversary class.

The adversary outputs an annotated ledger: each transaction paired with the announced
representation of its commitment and binding key. Being algebraic is the pair of hypotheses
`halgLabel` and `halgOut`: query-time labels and announced representations evaluate to the
transactions' actual elements. The extractor (`kappaExtractor`) reads the `key` coefficient
at the ℛ slot of the representation in effect at the signature's query point; it is defined
per sample and obtains that representation from the run's own data, so no representation
appears among the `Extractor` interface's arguments (the caveat in
`Ledger/ExtractionArm.lean`). A key without a pivot is on the ℛ line, where the extractor
succeeds, so an extraction failure lands in the knowledge-error event's pivot arm. The
failing transaction is recovered oracle-free from the annotated output (`failTxOfAnn`), so
the composite machine returning its signature data is covered by the knowledge-error bound
at an unchanged query count; validity of the output ledger is a conjunct of the bounded
event, as in `Ledger/KeyBindingArm.lean`.
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Security.BindingSignature Zcash.Security.RedDSA Zcash.Snark
open Zcash.Snark.LabeledOracleComp
open scoped ENNReal

universe u

variable {r : ℕ} [Fact (Nat.Prime r)]
variable {G : Type*} [AddCommGroup G] [Module (ZMod r) G] [DecidableEq G]
variable {Q : Type u} [Fintype Q] [DecidableEq Q] [Inhabited Q]
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}
variable (m : ℕ)

section OracleModel

variable (gen : G) (v_idx r_idx : Fin m) (queryOf : G → G → MSG → Q)
  (P₀ : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG)
  (toSig : SIG → RedDSA.Sig (ZMod r) G)

/-- The primitives at a sampled challenge table `O` and basis logs `s`. The value commitment
is the Pedersen commitment at the sampled slots `𝒱 = [s v_idx] gen`, `ℛ = [s r_idx] gen`.
Binding verification is the Schnorr equation at base ℛ, with the challenge read off the table
at the query point `queryOf R vk m`. A record update of `P₀`, so the tree depth — and with it
the ledger type — does not depend on the sample. -/
def kappaPrimitivesAt (O : Q → ZMod r) (s : Fin m → ZMod r) :
    Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG :=
  { P₀ with
    valueCommit := fun v rcv => (v : ZMod r) • (s v_idx • gen) + rcv • (s r_idx • gen)
    bindingVerify := fun vk m σ =>
      (toSig σ).S • (s r_idx • gen)
        = (toSig σ).R + O (queryOf (toSig σ).R vk m) • vk }

/-- The value-commitment shape at the sampled bases. -/
def kappaShapeAt (O : Q → ZMod r) (s : Fin m → ZMod r) :
    ValueShape (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig O s) :=
  ⟨s v_idx • gen, s r_idx • gen, fun _ _ => rfl⟩

/-- The RedDSA shape at the sampled table and bases: the scheme based at ℛ whose challenge
hash reads the table at the query point. Its verification equation is definitionally what
`kappaPrimitivesAt`'s `bindingVerify` states. -/
def kappaBindingAt (O : Q → ZMod r) (s : Fin m → ZMod r) :
    BindingSigShape (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig O s)
      (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig O s) :=
  { sch := ⟨s r_idx • gen, fun R vk m => O (queryOf R vk m)⟩
    toSig := toSig
    base_eq := rfl
    verify_iff := fun _ _ _ => Iff.rfl }

/-- A transaction's binding verification key, computed from the presented bases: the machine
receives the bases, not their logs, so this is an oracle-free function of its inputs. At
`b = scalarBasis gen s` it is `Tx.bvk` of the sampled primitives. -/
def bvkAt (b : Fin m → G) (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth) : G :=
  (tx.actions.map fun a => a.inst.cv_net).sum
    - ((tx.vBalance : ZMod r) • b v_idx + (0 : ZMod r) • b r_idx)

omit [DecidableEq G] [Fintype Q] [DecidableEq Q] [Inhabited Q] in
theorem bvkAt_eq (O : Q → ZMod r) (s : Fin m → ZMod r)
    (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth) :
    bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx
      = tx.bvk (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig O s) :=
  rfl

/-- The first transaction of the length-`i` prefix failing the net-value equation, paired
with its announced representation: the transaction at which the conservation reduction's
premiss breaks, recovered oracle-free from the annotated ledger. -/
def failTxOfAnn
    (L : List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))
    (i : ℕ) :
    Option (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m) :=
  (L.take i).find? fun p => decide (txNetValue p.1 ≠ p.1.vBalance)

end OracleModel

section Identification

variable {P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}
variable {ledger : Ledger KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}

/-- The extraction-failure arm's exhibited data, identified with the searched list's first
imbalanced transaction: `find?` selects `tx`, and the failure's components are that
transaction's signature data. Computed data, in the breaks-as-computed-data style. -/
structure ExtractFailSelection {S : ValueShape P} (B : BindingSigShape P S)
    {E : RedDSA.Extractor (ZMod r) G MSG} (e : RedDSA.ExtractionFailure B.sch E)
    (L : List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth)) where
  tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth
  find : L.find? (fun tx => decide (txNetValue tx ≠ tx.vBalance)) = some tx
  vk_eq : e.vk = tx.bvk P
  m_eq : e.m = tx.sighash
  σ_eq : e.σ = B.toSig tx.bindingSig

/-- The premiss fold's extraction-failure arm breaks at the first transaction of the list
failing the net-value equation; the selection is computed from the fold hypothesis. -/
def allConservedOrBreak_extractFail
    (hval : ValidLedger P kv issuance maxActions ledger)
    (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG)
    (L : List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth))
    (hL : ∀ tx ∈ L, tx ∈ ledger)
    {e : RedDSA.ExtractionFailure B.sch E}
    (h : allConservedOrBreak (fun tx htx => S.premissOrBreakFallible B hval hr E tx htx) L hL
        = .inr (.inr e)) :
    ExtractFailSelection B e L := by
  induction L with
  | nil => simp [allConservedOrBreak] at h
  | cons tx t ih =>
      rw [allConservedOrBreak] at h
      by_cases heq : txNetValue tx = tx.vBalance
      · rw [ValueShape.premissOrBreakFallible] at h
        rw [dif_pos heq] at h
        simp only at h
        split at h
        next b hb =>
          simp only [PSum.inr.injEq] at h
          subst h
          obtain ⟨tx', hfind, hvk, hm, hσ⟩ := ih _ hb
          refine ⟨tx', ?_, hvk, hm, hσ⟩
          rw [List.find?_cons_of_neg (by simp [heq]), hfind]
        next hall => exact absurd h (by simp)
      · rw [ValueShape.premissOrBreakFallible] at h
        rw [dif_neg heq] at h
        by_cases hex : tx.bvk P
            = E (tx.bvk P) tx.sighash (B.toSig tx.bindingSig) • S.Rbase
        · rw [dif_pos hex] at h
          exact absurd h (by simp)
        · rw [dif_neg hex] at h
          simp only [PSum.inr.injEq] at h
          subst h
          exact ⟨tx, List.find?_cons_of_pos (by simp [heq]), rfl, rfl, rfl⟩

/-- The conservation reduction's extraction-failure arm at prefix `i` breaks at the prefix's
first imbalanced transaction; the selection is computed from the reduction hypothesis. -/
def balanceConservationOrBreak_extractFail
    (hval : ValidLedger P kv issuance maxActions ledger)
    (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ)
    {e : RedDSA.ExtractionFailure B.sch E}
    (h : balanceConservationOrBreak (issuance := issuance)
        (fun tx htx => S.premissOrBreakFallible B hval hr E tx htx) i = .inr (.inr e)) :
    ExtractFailSelection B e (ledger.take i) := by
  rw [balanceConservationOrBreak] at h
  split at h
  next b hb =>
    simp only [PSum.inr.injEq] at h
    subst h
    exact allConservedOrBreak_extractFail hval S B hr E _ _ hb
  next hall => exact absurd h (by simp)

end Identification

section ArmBound

variable (gen : G) (v_idx r_idx : Fin m) (queryOf : G → G → MSG → Q)
  (P₀ : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG)
  (toSig : SIG → RedDSA.Sig (ZMod r) G)
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- The composite machine's output: the response, challenge-query point, and announced
representation of the failing transaction's binding signature — an oracle-free function of
the presented bases and the adversary's annotated output. -/
def kappaOut (i : ℕ) (b : Fin m → G)
    (L : List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)) :
    KappaOutput (ZMod r) Q m :=
  match failTxOfAnn m P₀ L i with
  | some p =>
      ⟨(toSig p.1.bindingSig).S,
        queryOf (toSig p.1.bindingSig).R (bvkAt m v_idx r_idx P₀ b p.1) p.1.sighash,
        p.2⟩
  | none => default

/-- The composite knowledge-error adversary: run the labeled ledger adversary and return the
failing transaction's signature data. -/
def kappaComposite (i : ℕ)
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))) :
    (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (KappaOutput (ZMod r) Q m) :=
  fun b => (LA b).bind fun L => .pure (kappaOut m v_idx r_idx queryOf P₀ toSig i b L)

omit [Fintype Q] [DecidableEq Q] [DecidableEq G] in
/-- Post-processing the annotated ledger costs no queries. -/
theorem kappaComposite_queryBound {i : ℕ}
    {LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {qH : ℕ} {b : Fin m → G} (h : (LA b).QueryBound qH) :
    (kappaComposite m v_idx r_idx queryOf P₀ toSig i LA b).QueryBound qH := by
  have h' := OracleComp.queryBound_bind h
    (fun L => OracleComp.QueryBound.pure (kappaOut m v_idx r_idx queryOf P₀ toSig i b L) 0)
  simpa [LabeledOracleComp.QueryBound, kappaComposite] using h'

/-- The extractor at one sample: read the `key` coefficient at the ℛ slot off the
representation in effect at the triple's query point — the run's first annotation there when
one exists, and otherwise the announced representation of the prefix's first imbalanced
transaction (the one transaction at which the conservation reduction consults the
extractor). -/
def kappaExtractor (i : ℕ)
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (O : Q → ZMod r) (s : Fin m → ZMod r) : RedDSA.Extractor (ZMod r) G MSG :=
  fun vk msg σ =>
    match (LA (scalarBasis gen s)).findLabel O (queryOf σ.R vk msg) with
    | some ℓ => ℓ.key r_idx
    | none =>
        ((failTxOfAnn m P₀ ((LA (scalarBasis gen s)).run O) i).map
          fun p => p.2.key r_idx).getD 0

/-- `List.find?` over a prefix is stable under extending the prefix: the first match in
`l.take i` is the first match in `l.take k` for any `k ≥ i`. -/
theorem find?_take_eq_some_of_le {α : Type*} {p : α → Bool} {l : List α} {i k : ℕ}
    (hik : i ≤ k) {x : α} (h : (l.take i).find? p = some x) :
    (l.take k).find? p = some x := by
  have hsplit : l.take k = l.take i ++ (l.take k).drop i := by
    conv_lhs => rw [← List.take_append_drop i (l.take k)]
    rw [List.take_take, Nat.min_eq_left hik]
  rw [hsplit, List.find?_append, h]
  rfl

omit [Fintype Q] in
/-- An extraction-failure sample lands in the knowledge-error event of the prefix-`k`
composite, for any `k` at least the failing prefix: the arm breaks at the first imbalanced
transaction of its prefix, which is the same transaction for every prefix containing it
(`find?_take_eq_some_of_le`), so one machine serves every prefix it covers. -/
theorem extractFail_mem_kappaEvent
    {LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    (halgLabel : ∀ (O : Q → ZMod r) (s : Fin m → ZMod r) (q : Q) (ℓ : QueryRep (ZMod r) m),
      (LA (scalarBasis gen s)).findLabel O q = some ℓ →
      ∀ p ∈ (LA (scalarBasis gen s)).run O,
        queryOf (toSig p.1.bindingSig).R (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1)
            p.1.sighash = q →
          (toSig p.1.bindingSig).R = representationEval (scalarBasis gen s) ℓ.commitment
          ∧ bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1
            = representationEval (scalarBasis gen s) ℓ.key)
    (halgOut : ∀ (O : Q → ZMod r) (s : Fin m → ZMod r),
      ∀ p ∈ (LA (scalarBasis gen s)).run O,
        (toSig p.1.bindingSig).R = representationEval (scalarBasis gen s) p.2.commitment
        ∧ bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1
          = representationEval (scalarBasis gen s) p.2.key)
    (hr : (maxActions + 1) * P₀.valueBound ≤ r) {i k : ℕ} (hik : i ≤ k)
    {O : Q → ZMod r} {s : Fin m → ZMod r}
    (hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig O s) kv issuance
      maxActions (((LA (scalarBasis gen s)).run O).map Prod.fst))
    {e : RedDSA.ExtractionFailure (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig O s).sch
      (kappaExtractor m gen r_idx queryOf P₀ k LA O s)}
    (heq : balanceConservationOrBreak (issuance := issuance)
        (fun tx htx => (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig O s)
          |>.premissOrBreakFallible (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig O s)
            hval hr (kappaExtractor m gen r_idx queryOf P₀ k LA O s) tx htx) i
      = .inr (.inr e)) :
    (O, s) ∈ kappaEvent m gen r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) := by
  obtain ⟨tx, hfind, hvk, hm, hσ⟩ :=
    balanceConservationOrBreak_extractFail hval _ _ hr
      (kappaExtractor m gen r_idx queryOf P₀ k LA O s) i heq
  have hvk' : e.vk = bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx := hvk
  have hσ' : e.σ = toSig tx.bindingSig := hσ
  -- lift the first-failure selection to the annotated ledger
  obtain ⟨pr, hpr, hfst⟩ : ∃ pr,
      failTxOfAnn m P₀ ((LA (scalarBasis gen s)).run O) i = some pr ∧ pr.1 = tx := by
    rw [← List.map_take, List.find?_map] at hfind
    obtain ⟨pr, hpr, hfst⟩ := Option.map_eq_some_iff.mp hfind
    exact ⟨pr, hpr, hfst⟩
  obtain ⟨rep, rfl⟩ : ∃ rep, pr = (tx, rep) := ⟨pr.2, by rw [← hfst, Prod.mk.eta]⟩
  have hfindAnnK : failTxOfAnn m P₀ ((LA (scalarBasis gen s)).run O) k = some (tx, rep) :=
    find?_take_eq_some_of_le hik hpr
  have hmem : (tx, rep) ∈ (LA (scalarBasis gen s)).run O :=
    (List.take_sublist k _).subset (List.mem_of_find?_eq_some hfindAnnK)
  have hout : dischargeOut m gen (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) O s
      = ⟨(toSig tx.bindingSig).S,
          queryOf (toSig tx.bindingSig).R (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx)
            tx.sighash,
          rep⟩ := by
    simp only [dischargeOut, kappaComposite, LabeledOracleComp.run_bind,
      LabeledOracleComp.run_pure, kappaOut]
    rw [hfindAnnK]
  have heff : effectiveRep m gen (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) O s
      = ((LA (scalarBasis gen s)).findLabel O
          (queryOf (toSig tx.bindingSig).R (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx)
            tx.sighash)).getD rep := by
    unfold effectiveRep
    rw [hout]
    simp only [kappaComposite, LabeledOracleComp.findLabel_bind_pure]
  have hRB : (toSig tx.bindingSig).R
        = representationEval (scalarBasis gen s)
            (effectiveRep m gen (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) O s).commitment
      ∧ bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx
        = representationEval (scalarBasis gen s)
            (effectiveRep m gen (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) O s).key := by
    rw [heff]
    cases hfound : (LA (scalarBasis gen s)).findLabel O
        (queryOf (toSig tx.bindingSig).R (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx)
          tx.sighash) with
    | some ℓ => simpa using halgLabel O s _ ℓ hfound (tx, rep) hmem rfl
    | none => simpa using halgOut O s (tx, rep) hmem
  have hEval : kappaExtractor m gen r_idx queryOf P₀ k LA O s e.vk e.m e.σ
      = (effectiveRep m gen (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) O s).key r_idx := by
    rw [hvk', hm, hσ', heff]
    unfold kappaExtractor
    cases (LA (scalarBasis gen s)).findLabel O
        (queryOf (toSig tx.bindingSig).R (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx)
          tx.sighash) <;>
      simp [hfindAnnK]
    rfl
  constructor
  · -- the game's verification equation, from the ledger's, through the effective evaluations
    unfold Verifies dischargeChallenge
    rw [hout]
    dsimp only
    rw [← hRB.1, ← hRB.2]
    have hver := e.verifies
    rw [hvk, hm, hσ] at hver
    exact hver
  · -- a pivot-free effective key would make the extractor succeed
    rcases hpiv : (effectiveRep m gen
        (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) O s).pivot r_idx with _ | j
    · exfalso
      have hkey := QueryRep.representationEval_key_of_pivot_eq_none
        (effectiveRep m gen (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) O s) r_idx
        (scalarBasis gen s) hpiv
      apply e.ne
      rw [hEval, hvk', hRB.2, hkey]
      rfl
    · rfl

/-- **The extraction-failure arm's κ, discharged.** For any `qH`-query-bounded labeled
algebraic ledger adversary in the challenge-oracle model, the probability that its output
ledger is valid and the conservation reduction at prefix `i`, with the effective-representation
extractor, lands in the extraction-failure arm is at most
`(qH+1)/|F| + (ε + 1/|F|) = (qH+2)/|F| + ε`. `halgLabel` and `halgOut` model the hypothesis
that the adversary is algebraic: query-time labels and announced representations evaluate to
the transactions' actual elements at their query points. The bound takes textbook-DL
advantage at most `ε` for the relation finder replaying the composite. The failing
transaction is recovered oracle-free (`balanceConservationOrBreak_extractFail`), so the
composite is covered by the knowledge-error bound at an unchanged query count. Validity of
the output ledger is a conjunct of the measured event, not something the composite decides:
its meaning depends on the sampled primitives, which an oracle machine's result type cannot
mention (as in `Ledger/KeyBindingArm.lean`). -/
theorem balanceConservation_extractFailArm_measure_le {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {qH : ℕ} (hQ : ∀ j b, (LA j b).QueryBound qH)
    (halgLabel : ∀ (j : ι) (O : Q → ZMod r) (s : Fin m → ZMod r) (q : Q)
      (ℓ : QueryRep (ZMod r) m),
      (LA j (scalarBasis gen s)).findLabel O q = some ℓ →
      ∀ p ∈ (LA j (scalarBasis gen s)).run O,
        queryOf (toSig p.1.bindingSig).R (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1)
            p.1.sighash = q →
          (toSig p.1.bindingSig).R = representationEval (scalarBasis gen s) ℓ.commitment
          ∧ bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1
            = representationEval (scalarBasis gen s) ℓ.key)
    (halgOut : ∀ (j : ι) (O : Q → ZMod r) (s : Fin m → ZMod r),
      ∀ p ∈ (LA j (scalarBasis gen s)).run O,
        (toSig p.1.bindingSig).R = representationEval (scalarBasis gen s) p.2.commitment
        ∧ bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1
          = representationEval (scalarBasis gen s) p.2.key)
    (hr : (maxActions + 1) * P₀.valueBound ≤ r) (i : ℕ) {ε : ℝ≥0∞}
    (hdl : ∀ (j : ι) (O : Q → ZMod r),
      TextbookDLAdvantageLE gen
        (relFinder m r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig i (LA j)) O) ε) :
    ((p.bind fun j =>
        (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).map (Prod.mk j))).toOuterMeasure
        (setOf fun (x : ι × ((Q → ZMod r) × (Fin m → ZMod r))) =>
          ∃ hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
              kv issuance maxActions
              (((LA x.1 (scalarBasis gen x.2.2)).run x.2.1).map Prod.fst),
            ∃ e, balanceConservationOrBreak (issuance := issuance)
                (fun tx htx => (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
                  |>.premissOrBreakFallible
                    (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
                    hval hr
                    (kappaExtractor m gen r_idx queryOf P₀ i (LA x.1) x.2.1 x.2.2)
                    tx htx) i
              = .inr (.inr e))
      ≤ ((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) + ε := by
  refine Zcash.Security.KeyBinding.toOuterMeasure_bind_le _ _ _ fun j => ?_
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans (le_trans (MeasureTheory.measure_mono ?hsub)
    (kappaEvent_measure_le m gen r_idx
      (kappaComposite m v_idx r_idx queryOf P₀ toSig i (LA j))
      (fun s => kappaComposite_queryBound m v_idx r_idx queryOf P₀ toSig (hQ j _))
      (hdl j))) (le_of_eq ?heq)
  case heq =>
    rw [add_comm ε, ← add_assoc, ENNReal.div_add_div_same]
    norm_cast
  rintro ⟨O, s⟩ ⟨hval, e, heq⟩
  dsimp only at hval heq
  exact extractFail_mem_kappaEvent m gen v_idx r_idx queryOf P₀ toSig
    (halgLabel j) (halgOut j) hr le_rfl hval heq

/-- **The all-prefixes extraction-failure arm's κ, discharged with no factor of `k`.** As
`balanceConservation_extractFailArm_measure_le`, over the event that the reduction lands in
the extraction-failure arm at *some* prefix `i < k`. Every such prefix breaks at the
ledger's first imbalanced transaction — the same transaction for every prefix containing
it — so the one prefix-`k` composite covers them all and the bound is unchanged. -/
theorem balanceConservationBefore_extractFailArm_measure_le {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {qH : ℕ} (hQ : ∀ j b, (LA j b).QueryBound qH)
    (halgLabel : ∀ (j : ι) (O : Q → ZMod r) (s : Fin m → ZMod r) (q : Q)
      (ℓ : QueryRep (ZMod r) m),
      (LA j (scalarBasis gen s)).findLabel O q = some ℓ →
      ∀ p ∈ (LA j (scalarBasis gen s)).run O,
        queryOf (toSig p.1.bindingSig).R (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1)
            p.1.sighash = q →
          (toSig p.1.bindingSig).R = representationEval (scalarBasis gen s) ℓ.commitment
          ∧ bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1
            = representationEval (scalarBasis gen s) ℓ.key)
    (halgOut : ∀ (j : ι) (O : Q → ZMod r) (s : Fin m → ZMod r),
      ∀ p ∈ (LA j (scalarBasis gen s)).run O,
        (toSig p.1.bindingSig).R = representationEval (scalarBasis gen s) p.2.commitment
        ∧ bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1
          = representationEval (scalarBasis gen s) p.2.key)
    (hr : (maxActions + 1) * P₀.valueBound ≤ r) (k : ℕ) {ε : ℝ≥0∞}
    (hdl : ∀ (j : ι) (O : Q → ZMod r),
      TextbookDLAdvantageLE gen
        (relFinder m r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j)) O) ε) :
    ((p.bind fun j =>
        (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).map (Prod.mk j))).toOuterMeasure
        (setOf fun (x : ι × ((Q → ZMod r) × (Fin m → ZMod r))) =>
          ∃ hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
              kv issuance maxActions
              (((LA x.1 (scalarBasis gen x.2.2)).run x.2.1).map Prod.fst),
            ∃ i, i < k ∧ ∃ e, balanceConservationOrBreak (issuance := issuance)
                (fun tx htx => (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
                  |>.premissOrBreakFallible
                    (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
                    hval hr
                    (kappaExtractor m gen r_idx queryOf P₀ k (LA x.1) x.2.1 x.2.2)
                    tx htx) i
              = .inr (.inr e))
      ≤ ((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) + ε := by
  refine Zcash.Security.KeyBinding.toOuterMeasure_bind_le _ _ _ fun j => ?_
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans (le_trans (MeasureTheory.measure_mono ?hsub)
    (kappaEvent_measure_le m gen r_idx
      (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j))
      (fun s => kappaComposite_queryBound m v_idx r_idx queryOf P₀ toSig (hQ j _))
      (hdl j))) (le_of_eq ?heq)
  case heq =>
    rw [add_comm ε, ← add_assoc, ENNReal.div_add_div_same]
    norm_cast
  rintro ⟨O, s⟩ ⟨hval, i, hik, e, heq⟩
  dsimp only at hval heq
  exact extractFail_mem_kappaEvent m gen v_idx r_idx queryOf P₀ toSig
    (halgLabel j) (halgOut j) hr (le_of_lt hik) hval heq

end ArmBound

end Zcash.Security.Ledger.Model
