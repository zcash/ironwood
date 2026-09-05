import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Ledger.ExtractionArm
import Zcash.Security.RedDSA.KnowledgeError
import Zcash.Security.KeyBinding.Probability

/-!
# The extraction-failure arm's κ in the oracle model

The capstone layer bounds the conservation reduction's extraction-failure arm by the named
knowledge error κ — the probability that a binding signature verifies while binding-key
extraction fails (`Zcash.Security.RedDSA.KnowledgeError`). This module places that arm in
the challenge-oracle model, at the reduction's own events: for any `qH`-query-bounded
labeled algebraic ledger adversary, an extraction-failure sample lands in the knowledge-error
event of the composite machine at an unchanged query count (`extractFail_mem_kappaEventAt`).
The knowledge-error layer splits that event into two fibres. The bad-challenge fibre is
counted at `(qH+1)/#F`. The relation fibre is covered by the conservation experiment's
combined finder, under one discrete-log bound. As with the key-binding arm, the bounds here
are on the joint event that the ledger is valid and extraction fails, not on extraction
failure alone. The capstones' named κ ranges over an abstract `PMF (ValidAnnotated …)`; the
conservation experiment is the joint-experiment composition, and bounds the challenge-oracle
measure directly.

The sample is a challenge table `table` and the discrete logarithms `logs`, relative to
the generator `gen`, of the `m` presented bases. The value commitment and the binding
verification are instantiated at sampled slots, as a record update of the fixed primitives
(`kappaPrimitivesAt`), so the ledger type does not depend on the sample; the other
primitives deliberately stay fixed, and the value and signature fields are not separated
out of `Primitives`. The `kappa` prefix marks the sampled forms that the knowledge-error
analysis consumes. The challenge hash reads the table at `queryOf R bvk m`, intended to be
an injective encoding — collisions only constrain the algebraic hypotheses, shrinking the
covered adversary class.

The adversary outputs an annotated ledger: each transaction paired with the announced
representation of its commitment and binding key. Being algebraic is the
`AlgebraicAtBindingPoints` structure: its `atLabel` and `atOutput` fields say that
query-time labels and announced representations evaluate to the transactions' actual
elements. The extractor (`kappaExtractor`) reads the `key` coefficient at the ℛ slot of the
representation in effect at the signature's query point; it is defined per sample and
obtains that representation from the run's own data, so no representation appears among the
`Extractor` interface's arguments (the caveat in `Ledger/ExtractionArm.lean`). A key without
a pivot is on the ℛ line, where the extractor succeeds, so an extraction failure lands in
the knowledge-error event's pivot arm. The failing transaction is recovered oracle-free from
the annotated output (`failTxOfAnn`), so the composite machine returning its signature data
is covered by the knowledge-error bound at an unchanged query count; validity of the output
ledger is a conjunct of the bounded event, as in `Ledger/KeyBindingArm.lean`.
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Security.BindingSignature Zcash.Security.RedDSA Zcash.Snark
open Zcash.Common Zcash.Common.LabeledOracleComp
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

/-- The primitives at a presented `basis` and challenge table `table`. The value commitment
is the Pedersen commitment at the slots `𝒱 = basis v_idx`, `ℛ = basis r_idx`. Binding verification
is the Schnorr equation at base ℛ, with the challenge read off the table at the query point
`queryOf R vk m`. A record update of `P₀`, so the tree depth —and with it the ledger
type— depends on neither the basis nor the table. -/
def primitivesAtBasis (basis : Fin m → G) (table : Q → ZMod r) :
    Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG :=
  { P₀ with
    valueCommit := fun v rcv => (v : ZMod r) • basis v_idx + rcv • basis r_idx
    bindingVerify := fun vk m σ =>
      (toSig σ).S • basis r_idx
        = (toSig σ).R + table (queryOf (toSig σ).R vk m) • vk }

/-- The primitives at a sampled challenge table `table` and the basis discrete logarithms `logs`:
`primitivesAtBasis` at the sampled basis. The `kappa` prefix marks the sampled forms that the
knowledge-error (κ) analysis consumes — see `Zcash.Security.RedDSA.KnowledgeError`. -/
def kappaPrimitivesAt (table : Q → ZMod r) (logs : Fin m → ZMod r) :
    Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG :=
  primitivesAtBasis m v_idx r_idx queryOf P₀ toSig (scalarBasis gen logs) table

/-- The value-commitment shape at the presented basis. -/
def shapeAtBasis (basis : Fin m → G) (table : Q → ZMod r) :
    ValueShape (primitivesAtBasis m v_idx r_idx queryOf P₀ toSig basis table) :=
  ⟨basis v_idx, basis r_idx, fun _ _ => rfl⟩

/-- The value-commitment shape at the sampled bases: `shapeAtBasis` at the sampled basis. -/
def kappaShapeAt (table : Q → ZMod r) (logs : Fin m → ZMod r) :
    ValueShape (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig table logs) :=
  shapeAtBasis m v_idx r_idx queryOf P₀ toSig (scalarBasis gen logs) table

/-- The RedDSA shape at the presented basis and table: the scheme based at ℛ whose challenge
hash reads the table at the query point. Its verification equation is definitionally what
`primitivesAtBasis`'s `bindingVerify` states. -/
def bindingAtBasis (basis : Fin m → G) (table : Q → ZMod r) :
    BindingSigShape (primitivesAtBasis m v_idx r_idx queryOf P₀ toSig basis table)
      (shapeAtBasis m v_idx r_idx queryOf P₀ toSig basis table) :=
  { sch := ⟨basis r_idx, fun R vk m => table (queryOf R vk m)⟩
    toSig := toSig
    base_eq := rfl
    verify_iff := fun _ _ _ => Iff.rfl }

/-- The RedDSA shape at the sampled table and bases: `bindingAtBasis` at the sampled
basis. -/
def kappaBindingAt (table : Q → ZMod r) (logs : Fin m → ZMod r) :
    BindingSigShape (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig table logs)
      (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig table logs) :=
  bindingAtBasis m v_idx r_idx queryOf P₀ toSig (scalarBasis gen logs) table

/-- A transaction's binding verification key, computed from the presented bases: the machine
receives the bases, not their logs, so this is an oracle-free function of its inputs. At
`basis = scalarBasis gen logs` it is `Tx.bvk` of the sampled primitives. -/
def bvkAt (basis : Fin m → G) (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth) : G :=
  (tx.actions.map fun a => a.inst.cv_net).sum
    - ((tx.vBalance : ZMod r) • basis v_idx + (0 : ZMod r) • basis r_idx)

omit [DecidableEq G] [Fintype Q] [DecidableEq Q] [Inhabited Q] in
theorem bvkAt_eq (table : Q → ZMod r) (logs : Fin m → ZMod r)
    (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth) :
    bvkAt m v_idx r_idx P₀ (scalarBasis gen logs) tx
      = tx.bvk (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig table logs) :=
  rfl

/-- **The adversary is algebraic at the binding-signature points, at the presented `basis`.**
For each transaction it outputs, and at each challenge query it makes, the adversary
announces how it built two group elements out of the presented basis: the binding signature's
nonce `R`, and the transaction's binding verification key `bvk`. Each announcement is a
`QueryRep`: a pair of coefficient vectors, one for `R` and one for `bvk`. On its own that is
only a claim — nothing in the type forces the coefficients to be correct. This structure is
the assumption that they are correct: each vector, evaluated against the presented basis by
`representationEval`, yields the group element it names (`R` from the commitment vector,
`bvk` from the key vector).

This module's docstring explains why the reduction needs the assumption, and why only at
these two points. Consumed by `extractFail_mem_kappaEventAt`. -/
structure AlgebraicAtBindingPointsAt (basis : Fin m → G)
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))) :
    Prop where
  /-- At query time: the label recorded at a challenge query represents the querying
  transaction's nonce and binding key. The half that pins the query's one bad challenge before
  the oracle answers. -/
  atLabel : ∀ (table : Q → ZMod r) (query : Q) (ℓ : QueryRep (ZMod r) m),
    (LA basis).findLabel table query = some ℓ →
    ∀ tx_rep ∈ (LA basis).run table,
      queryOf (toSig tx_rep.1.bindingSig).R (bvkAt m v_idx r_idx P₀ basis tx_rep.1)
          tx_rep.1.sighash = query →
        (toSig tx_rep.1.bindingSig).R = representationEval basis ℓ.commitment
        ∧ bvkAt m v_idx r_idx P₀ basis tx_rep.1 = representationEval basis ℓ.key
  /-- At output time: each transaction's announced representation represents its own nonce and
  binding key. The half the extractor falls back on when the run never queried that point. -/
  atOutput : ∀ (table : Q → ZMod r),
    ∀ tx_rep ∈ (LA basis).run table,
      (toSig tx_rep.1.bindingSig).R = representationEval basis tx_rep.2.commitment
      ∧ bvkAt m v_idx r_idx P₀ basis tx_rep.1 = representationEval basis tx_rep.2.key

/-- The algebraicity assumption at every sampled basis: `AlgebraicAtBindingPointsAt` at
`scalarBasis gen logs`, for every choice of `logs`. The experiments take this form and
apply it at their sample's basis. -/
def AlgebraicAtBindingPoints
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))) :
    Prop :=
  ∀ logs : Fin m → ZMod r,
    AlgebraicAtBindingPointsAt m v_idx r_idx queryOf P₀ toSig (scalarBasis gen logs) LA

/-- The first transaction of the length-`i` prefix failing the net-value equation, paired
with its announced representation: the transaction at which the conservation reduction's
premiss breaks, recovered oracle-free from the annotated ledger. -/
def failTxOfAnn
    (L : List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))
    (i : ℕ) :
    Option (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m) :=
  (L.take i).find? fun tx_rep => decide (txNetValue tx_rep.1 ≠ tx_rep.1.vBalance)

end OracleModel

section Identification

variable {P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}
variable {ledger : Ledger KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}

/-- The extraction-failure arm's exhibited data, identified with the searched list's first
imbalanced transaction: `find?` selects `tx`, and the failure's components are that
transaction's signature data. Computed data, in the breaks-as-computed-data style. -/
structure ExtractFailSelection {shape : ValueShape P} (binding : BindingSigShape P shape)
    {extractor : RedDSA.Extractor (ZMod r) G MSG}
    (failure : RedDSA.ExtractionFailure binding.sch extractor)
    (L : List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth)) where
  tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth
  find : L.find? (fun tx => decide (txNetValue tx ≠ tx.vBalance)) = some tx
  vk_eq : failure.vk = tx.bvk P
  m_eq : failure.m = tx.sighash
  σ_eq : failure.σ = binding.toSig tx.bindingSig

/-- The premiss fold's extraction-failure arm breaks at the first transaction of the list
failing the net-value equation; the selection is computed from the fold hypothesis. -/
def allConservedOrBreak_extractFail
    (hval : ValidLedger P kv issuance maxActions ledger)
    (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG)
    (L : List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth))
    (hL : ∀ tx ∈ L, tx ∈ ledger)
    {failure : RedDSA.ExtractionFailure binding.sch extractor}
    (h : allConservedOrBreak
        (fun tx htx => shape.premissOrBreakFallible binding hval hr extractor tx htx) L hL
        = .inr (.inr failure)) :
    ExtractFailSelection binding failure L := by
  induction L with
  | nil => simp [allConservedOrBreak] at h
  | cons tx t ih =>
      rw [allConservedOrBreak] at h
      by_cases heq : txNetValue tx = tx.vBalance
      · rw [ValueShape.premissOrBreakFallible] at h
        rw [dif_pos heq] at h
        simp only at h
        split at h
        next brk hb =>
          simp only [PSum.inr.injEq] at h
          subst h
          obtain ⟨tx', hfind, hvk, hm, hσ⟩ := ih _ hb
          refine ⟨tx', ?_, hvk, hm, hσ⟩
          rw [List.find?_cons_of_neg (by simp [heq]), hfind]
        next hall => exact absurd h (by simp)
      · rw [ValueShape.premissOrBreakFallible] at h
        rw [dif_neg heq] at h
        by_cases hex : tx.bvk P
            = extractor (tx.bvk P) tx.sighash (binding.toSig tx.bindingSig) • shape.Rbase
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
    (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ)
    {failure : RedDSA.ExtractionFailure binding.sch extractor}
    (h : balanceConservationOrBreak (issuance := issuance)
        (fun tx htx => shape.premissOrBreakFallible binding hval hr extractor tx htx) i
      = .inr (.inr failure)) :
    ExtractFailSelection binding failure (ledger.take i) := by
  rw [balanceConservationOrBreak] at h
  split at h
  next brk hb =>
    simp only [PSum.inr.injEq] at h
    subst h
    exact allConservedOrBreak_extractFail hval shape binding hr extractor _ _ hb
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
def kappaOut (i : ℕ) (basis : Fin m → G)
    (L : List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)) :
    KappaOutput (ZMod r) Q m :=
  match failTxOfAnn m P₀ L i with
  | some tx_rep =>
      ⟨(toSig tx_rep.1.bindingSig).S,
        queryOf (toSig tx_rep.1.bindingSig).R (bvkAt m v_idx r_idx P₀ basis tx_rep.1)
          tx_rep.1.sighash,
        tx_rep.2⟩
  | none => default

/-- The composite knowledge-error adversary: run the labeled ledger adversary and return the
failing transaction's signature data. -/
def kappaComposite (i : ℕ)
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))) :
    (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (KappaOutput (ZMod r) Q m) :=
  fun basis => (LA basis).bind fun L => .pure (kappaOut m v_idx r_idx queryOf P₀ toSig i basis L)

omit [Fintype Q] [DecidableEq Q] [DecidableEq G] in
/-- Post-processing the annotated ledger costs no queries. -/
theorem kappaComposite_queryBound {i : ℕ}
    {LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {qH : ℕ} {basis : Fin m → G} (h : (LA basis).QueryBound qH) :
    (kappaComposite m v_idx r_idx queryOf P₀ toSig i LA basis).QueryBound qH := by
  have h' := OracleComp.queryBound_bind h
    (fun L => OracleComp.QueryBound.pure (kappaOut m v_idx r_idx queryOf P₀ toSig i basis L) 0)
  simpa [LabeledOracleComp.QueryBound, kappaComposite] using h'

/-- The extractor at a presented basis and table: read the `key` coefficient at the ℛ slot
off the representation in effect at the triple's query point — the run's first annotation
there when one exists, and otherwise the announced representation of the prefix's first
imbalanced transaction (the one transaction at which the conservation reduction consults the
extractor). -/
def extractorAtBasis (i : ℕ)
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (basis : Fin m → G) (table : Q → ZMod r) : RedDSA.Extractor (ZMod r) G MSG :=
  fun vk msg σ =>
    match (LA basis).findLabel table (queryOf σ.R vk msg) with
    | some ℓ => ℓ.key r_idx
    | none =>
        ((failTxOfAnn m P₀ ((LA basis).run table) i).map
          fun tx_rep => tx_rep.2.key r_idx).getD 0

/-- The extractor at one sample: `extractorAtBasis` at the sampled basis. -/
def kappaExtractor (i : ℕ)
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (table : Q → ZMod r) (logs : Fin m → ZMod r) : RedDSA.Extractor (ZMod r) G MSG :=
  extractorAtBasis m r_idx queryOf P₀ i LA (scalarBasis gen logs) table

/-- `List.find?` over a prefix is stable under extending the prefix: the first match in
`l.take i` is the first match in `l.take k` for any `k ≥ i`. -/
theorem find?_take_eq_some_of_le {α : Type*} {tx_rep : α → Bool} {l : List α} {i k : ℕ}
    (hik : i ≤ k) {x : α} (h : (l.take i).find? tx_rep = some x) :
    (l.take k).find? tx_rep = some x := by
  have hsplit : l.take k = l.take i ++ (l.take k).drop i := by
    conv_lhs => rw [← List.take_append_drop i (l.take k)]
    rw [List.take_take, Nat.min_eq_left hik]
  rw [hsplit, List.find?_append, h]
  rfl

omit [Fintype Q] in
/-- An extraction-failure sample at the presented `basis` lands in the per-basis
knowledge-error event of the prefix-`k` composite, for any `k` at least the failing prefix.
The arm breaks at the first imbalanced transaction of its prefix. That transaction is the
same for every prefix containing it (`find?_take_eq_some_of_le`), so one machine serves
every prefix it covers. -/
theorem extractFail_mem_kappaEventAt
    {LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {basis : Fin m → G}
    (halg : AlgebraicAtBindingPointsAt m v_idx r_idx queryOf P₀ toSig basis LA)
    (hr : maxActions * (P₀.valueBound - 1) + P₀.vBalanceBound < r) {i k : ℕ} (hik : i ≤ k)
    {table : Q → ZMod r}
    (hval : ValidLedger (primitivesAtBasis m v_idx r_idx queryOf P₀ toSig basis table) kv issuance
      maxActions (((LA basis).run table).map Prod.fst))
    {failure : RedDSA.ExtractionFailure
      (bindingAtBasis m v_idx r_idx queryOf P₀ toSig basis table).sch
      (extractorAtBasis m r_idx queryOf P₀ k LA basis table)}
    (heq : balanceConservationOrBreak (issuance := issuance)
        (fun tx htx => (shapeAtBasis m v_idx r_idx queryOf P₀ toSig basis table)
          |>.premissOrBreakFallible (bindingAtBasis m v_idx r_idx queryOf P₀ toSig basis table)
            hval hr (extractorAtBasis m r_idx queryOf P₀ k LA basis table) tx htx) i
      = .inr (.inr failure)) :
    table ∈ kappaEventAt m r_idx (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) basis := by
  obtain ⟨tx, hfind, hvk, hm, hσ⟩ :=
    balanceConservationOrBreak_extractFail hval _ _ hr
      (extractorAtBasis m r_idx queryOf P₀ k LA basis table) i heq
  have hvk' : failure.vk = bvkAt m v_idx r_idx P₀ basis tx := hvk
  have hσ' : failure.σ = toSig tx.bindingSig := hσ
  -- lift the first-failure selection to the annotated ledger
  obtain ⟨tx_rep, hpr, hfst⟩ : ∃ tx_rep,
      failTxOfAnn m P₀ ((LA basis).run table) i = some tx_rep ∧ tx_rep.1 = tx := by
    rw [← List.map_take, List.find?_map] at hfind
    obtain ⟨tx_rep, hpr, hfst⟩ := Option.map_eq_some_iff.mp hfind
    exact ⟨tx_rep, hpr, hfst⟩
  obtain ⟨rep, rfl⟩ : ∃ rep, tx_rep = (tx, rep) := ⟨tx_rep.2, by rw [← hfst, Prod.mk.eta]⟩
  have hfindAnnK : failTxOfAnn m P₀ ((LA basis).run table) k = some (tx, rep) :=
    find?_take_eq_some_of_le hik hpr
  have hmem : (tx, rep) ∈ (LA basis).run table :=
    (List.take_sublist k _).subset (List.mem_of_find?_eq_some hfindAnnK)
  have hout : dischargeOutAt m (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) basis table
      = ⟨(toSig tx.bindingSig).S,
          queryOf (toSig tx.bindingSig).R (bvkAt m v_idx r_idx P₀ basis tx) tx.sighash,
          rep⟩ := by
    simp only [dischargeOutAt, kappaComposite, LabeledOracleComp.run_bind,
      LabeledOracleComp.run_pure, kappaOut]
    rw [hfindAnnK]
  have heff : effectiveRepAt m (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) basis table
      = ((LA basis).findLabel table
          (queryOf (toSig tx.bindingSig).R (bvkAt m v_idx r_idx P₀ basis tx)
            tx.sighash)).getD rep := by
    unfold effectiveRepAt
    rw [hout]
    simp only [kappaComposite, LabeledOracleComp.findLabel_bind_pure]
  have hRB : (toSig tx.bindingSig).R
        = representationEval basis
            (effectiveRepAt m (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA)
              basis table).commitment
      ∧ bvkAt m v_idx r_idx P₀ basis tx
        = representationEval basis
            (effectiveRepAt m (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA)
              basis table).key := by
    rw [heff]
    cases hfound : (LA basis).findLabel table
        (queryOf (toSig tx.bindingSig).R (bvkAt m v_idx r_idx P₀ basis tx)
          tx.sighash) with
    | some ℓ => simpa using halg.atLabel table _ ℓ hfound (tx, rep) hmem rfl
    | none => simpa using halg.atOutput table (tx, rep) hmem
  have hEval : extractorAtBasis m r_idx queryOf P₀ k LA basis table failure.vk failure.m failure.σ
      = (effectiveRepAt m (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA)
          basis table).key r_idx := by
    rw [hvk', hm, hσ', heff]
    unfold extractorAtBasis
    cases (LA basis).findLabel table
        (queryOf (toSig tx.bindingSig).R (bvkAt m v_idx r_idx P₀ basis tx)
          tx.sighash) <;>
      simp [hfindAnnK]
    rfl
  constructor
  · -- the game's verification equation, from the ledger's, through the effective evaluations
    unfold VerifiesAt dischargeChallengeAt
    rw [hout]
    dsimp only
    rw [← hRB.1, ← hRB.2]
    have hver := failure.verifies
    rw [hvk, hm, hσ] at hver
    exact hver
  · -- a pivot-free effective key would make the extractor succeed
    rcases hpiv : (effectiveRepAt m (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA)
        basis table).pivot r_idx with _ | j
    · exfalso
      have hkey := QueryRep.representationEval_key_of_pivot_eq_none
        (effectiveRepAt m (kappaComposite m v_idx r_idx queryOf P₀ toSig k LA) basis table) r_idx
        basis hpiv
      apply failure.ne
      rw [hEval, hvk', hRB.2, hkey]
      rfl
    · rfl

end ArmBound

end Zcash.Security.Ledger.Model
