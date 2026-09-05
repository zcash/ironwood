import Zcash.Security.Ledger.IntegrityExperiment
import Zcash.Security.Ledger.OrchardCapstone
import Zcash.Security.BindingSignature.Orchard

/-!
# The Orchard integrity experiment with idealized knowledge soundness

The non-negativity arms collapse to one Sinsemilla DLR.

The abstract integrity experiment (`balanceIntegrityBefore_measure_le_experiment`) bounds a
balance-integrity violation by `ε_nonneg + conservation` over the challenge-oracle sample space,
taking the union of the three Balance-subset arms (Merkle, note-commitment, key-binding) as one
named bound `ε_nonneg`. This module discharges `ε_nonneg` at the Orchard instantiation: all three
arms collapse onto the single advantage of computing a nontrivial discrete-log relation among the
fixed Sinsemilla bases, exactly as `orchardBalanceIntegrity_measure_le` does at the deployed
capstone layer, but now over the challenge experiment's sample space.

This is a programmed-basis reduction (see "what a reduction in these models says",
<https://zcash.github.io/ironwood/formal-verification/security-models.html#what-a-reduction-in-these-models-says>):
the sampling programs only the value and binding bases — `kappaPrimitivesAt` (named for the
knowledge-error κ analysis that consumes it) is a record update of the deployed primitives
touching `valueCommit` and `bindingVerify` alone. The three non-negativity arms read only
the note-commitment, key-binding, and Merkle structure, which the programming leaves fixed.
A Balance-subset break at the sampled primitives is therefore the same data as at the
deployed primitives, and the deterministic Orchard reducers (`relationOfKeyBindingBreak`,
`relationOfNoteCommitBreak`, `relationOfMerkleCollision`) apply unchanged. This discharge needs no
value/binding-side hypotheses, so it is independent of the conservation side, which the abstract
experiment handles through its combined coin-consuming finder.

The deployed forms run the fixed-basis experiment at `orchardValueBases` — the deployed
𝒱^Orchard and ℛ^Orchard. The value commitment is then definitionally the deployed one, so no
reference-string heuristic is involved on the value side; only the binding challenge hash is
idealized as the table. The relation arm is the named `ε_valuedlr`: the probability that the
deployed finder returns a nontrivial relation over the named 𝒱/ℛ slots.
-/

-- The Orchard reducers carry Sinsemilla chunk exponents beyond the default threshold, as in
-- `MerkleDLR`; raise it so the relation terms elaborate without an unevaluated-power warning.
set_option exponentiation.threshold 600

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Common Zcash.Security.BindingSignature Zcash.Security.RedDSA Zcash.Snark
open Zcash.Common.LabeledOracleComp
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Pool
open Zcash.Security.Ledger.Model
open scoped ENNReal

universe u

variable {MSG SIG : Type*}
  (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
  (issuance : ℕ → ℕ) (maxActions : ℕ)
variable {Q : Type u} [Fintype Q] [DecidableEq Q] [Inhabited Q]
variable (m : ℕ) (gen : PallasGroup) (v_idx r_idx : Fin m)
  (queryOf : PallasGroup → PallasGroup → MSG → Q)
  (toSig : SIG → RedDSA.Sig Fq PallasGroup)

/-- A note-commitment break at a presented basis's primitives is one at the deployed
primitives. The break constrains only `noteCommit`, `extract`, and `valueBound`, and
`primitivesAtBasis` — a record update touching only `valueCommit` and `bindingVerify` — leaves
those three fields equal to the deployed ones, so every field transports by definitional
equality. (`NoteCommitBreak` is indexed by the whole primitives record, which the update does
change, so the two break types are not definitionally equal; rebuilding field-by-field is what
carries the break across.) -/
def noteCommitBreakAtBasis (basis : Fin m → PallasGroup) (table : Q → Fq)
    (nb : NoteCommitBreak (primitivesAtBasis m v_idx r_idx queryOf
      (primitives spendAuthVerify bindingVerify) toSig basis table)) :
    NoteCommitBreak (primitives spendAuthVerify bindingVerify) :=
  ⟨nb.rcm₁, nb.n₁, nb.rcm₂, nb.n₂, nb.cm₁, nb.cm₂, nb.ne, nb.open₁, nb.open₂, nb.extract_eq,
    nb.v₁_lt, nb.v₂_lt⟩

/-- A note-commitment break at the sampled primitives: `noteCommitBreakAtBasis` at the sampled
basis. -/
def noteCommitBreakOfKappa (table : Q → Fq) (logs : Fin m → Fq)
    (nb : NoteCommitBreak (kappaPrimitivesAt m gen v_idx r_idx queryOf
      (primitives spendAuthVerify bindingVerify) toSig table logs)) :
    NoteCommitBreak (primitives spendAuthVerify bindingVerify) :=
  noteCommitBreakAtBasis spendAuthVerify bindingVerify m v_idx r_idx queryOf toSig
    (scalarBasis gen logs) table nb

/-- **The Orchard Balance-subset reduction at a presented basis.** As
`orchardBalanceSubsetOrRelation`, but at `primitivesAtBasis`'s primitives — the deployed Orchard
primitives with the value and binding fields replaced by the presented slots. Those replaced
fields are not read by any Balance-subset arm, so the reduction routes each break through the
same Orchard reducer and lands in the same combined-basis relation. -/
def orchardBalanceSubsetOrRelationAtBasis (basis : Fin m → PallasGroup) (table : Q → Fq)
    {ledger : Ledger _ Fq PallasGroup Fp Fp Fp Encoding MSG SIG _}
    (hval : ValidLedger (primitivesAtBasis m v_idx r_idx queryOf
        (primitives spendAuthVerify bindingVerify) toSig basis table) keyBinding issuance
        maxActions ledger) (i : ℕ) :
    (nonZeroSpends ledger (i + 1) ≤ ↑(positionedOutputs ledger i))
      ⊕' NontrivialRelation (F := Fq) pallasS orchardPoints :=
  match balanceSubsetOrBreak hval i with
  | .inl hsub => .inl hsub
  | .inr (.keyBinding _ _ h) => .inr (relationOfKeyBindingBreak h)
  | .inr (.noteCommit nb) => .inr (relationOfNoteCommitBreak spendAuthVerify bindingVerify
      (noteCommitBreakAtBasis spendAuthVerify bindingVerify m v_idx r_idx queryOf toSig
        basis table nb))
  | .inr (.merkle c) => .inr (relationOfMerkleCollision c.2)

/-- The Orchard Balance-subset reduction at the sampled bases:
`orchardBalanceSubsetOrRelationAtBasis` at the sampled basis. -/
def kappaOrchardBalanceSubsetOrRelation (table : Q → Fq) (logs : Fin m → Fq)
    {ledger : Ledger _ Fq PallasGroup Fp Fp Fp Encoding MSG SIG _}
    (hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf
        (primitives spendAuthVerify bindingVerify) toSig table logs) keyBinding issuance maxActions
        ledger) (i : ℕ) :
    (nonZeroSpends ledger (i + 1) ≤ ↑(positionedOutputs ledger i))
      ⊕' NontrivialRelation (F := Fq) pallasS orchardPoints :=
  orchardBalanceSubsetOrRelationAtBasis spendAuthVerify bindingVerify issuance maxActions m
    v_idx r_idx queryOf toSig (scalarBasis gen logs) table hval i

omit [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- A Balance-subset break at a presented basis's primitives computes an Orchard Sinsemilla
relation: the total reduction cannot return the containment when handed a break, so it returns
a relation. -/
theorem orchardBalanceSubsetOrRelationAtBasis_inr_of_break (basis : Fin m → PallasGroup)
    (table : Q → Fq)
    {ledger : Ledger _ Fq PallasGroup Fp Fp Fp Encoding MSG SIG _}
    (hval : ValidLedger (primitivesAtBasis m v_idx r_idx queryOf
        (primitives spendAuthVerify bindingVerify) toSig basis table) keyBinding issuance
        maxActions ledger) (i : ℕ)
    {brk : BalanceBreak (primitivesAtBasis m v_idx r_idx queryOf
        (primitives spendAuthVerify bindingVerify) toSig basis table) keyBinding}
    (hb : balanceSubsetOrBreak hval i = .inr brk) :
    ∃ rel, orchardBalanceSubsetOrRelationAtBasis spendAuthVerify bindingVerify issuance
      maxActions m v_idx r_idx queryOf toSig basis table hval i = .inr rel := by
  unfold orchardBalanceSubsetOrRelationAtBasis
  rw [hb]
  cases brk <;> exact ⟨_, rfl⟩

omit [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- A Balance-subset break at the sampled primitives computes an Orchard Sinsemilla relation:
`orchardBalanceSubsetOrRelationAtBasis_inr_of_break` at the sampled basis. -/
theorem kappaOrchardBalanceSubsetOrRelation_inr_of_break (table : Q → Fq) (logs : Fin m → Fq)
    {ledger : Ledger _ Fq PallasGroup Fp Fp Fp Encoding MSG SIG _}
    (hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf
        (primitives spendAuthVerify bindingVerify) toSig table logs) keyBinding issuance maxActions
        ledger) (i : ℕ)
    {brk : BalanceBreak (kappaPrimitivesAt m gen v_idx r_idx queryOf
        (primitives spendAuthVerify bindingVerify) toSig table logs) keyBinding}
    (hb : balanceSubsetOrBreak hval i = .inr brk) :
    ∃ rel, kappaOrchardBalanceSubsetOrRelation spendAuthVerify bindingVerify issuance maxActions m gen v_idx r_idx
      queryOf toSig table logs hval i = .inr rel :=
  orchardBalanceSubsetOrRelationAtBasis_inr_of_break spendAuthVerify bindingVerify issuance
    maxActions m v_idx r_idx queryOf toSig (scalarBasis gen logs) table hval i hb

variable {ι : Type u}
  (LA : ι → (Fin m → PallasGroup) → LabeledOracleComp Q Fq (fun _ => QueryRep Fq m)
    (List (Tx (KeyBinding.Pool.Witness Fq PallasGroup Fp) Fq PallasGroup Fp Fp Fp Encoding MSG SIG
      (primitives spendAuthVerify bindingVerify).depth × QueryRep Fq m)))

/-- **The sampled Orchard Sinsemilla-relation event.** The samples on which the output ledger is
valid at the sampled primitives and its data computes a nontrivial discrete-log relation among the
fixed Sinsemilla bases at some step `i < k`. This is the challenge-experiment analogue of the
deployed capstone's `orchardRelationEventUpTo`; the single advantage `ε_sinsemilladlr` is a bound on
this one event. -/
def sampledOrchardRelationEventUpTo (k : ℕ) :
    Set (ι × ((Q → Fq) × (Fin m → Fq))) :=
  setOf fun x =>
    ∃ hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf
        (primitives spendAuthVerify bindingVerify) toSig x.2.1 x.2.2) keyBinding issuance maxActions
        (((LA x.1 (scalarBasis gen x.2.2)).run x.2.1).map Prod.fst),
      ∃ i, i < k ∧ ∃ rel, kappaOrchardBalanceSubsetOrRelation spendAuthVerify bindingVerify issuance maxActions
        m gen v_idx r_idx queryOf toSig x.2.1 x.2.2 hval i = .inr rel

omit [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- **The three sampled non-negativity arms collapse onto the Sinsemilla-relation event.** Every
sample on which the reduction lands in the Merkle, note-commitment, or key-binding arm computes a
nontrivial discrete-log relation among the fixed Sinsemilla bases: the arm's break is routed through
its deterministic Orchard reducer (`kappaOrchardBalanceSubsetOrRelation`). This is what discharges
the abstract experiment's combined `ε_nonneg` by the single `ε_sinsemilladlr` at the Orchard
instantiation. -/
theorem sampledBalanceSubsetArms_subset_orchardRelation (k : ℕ) :
    sampledLedgerEvent m gen v_idx r_idx queryOf (primitives spendAuthVerify bindingVerify) toSig LA
        (balanceSubsetArmsUpTo (kv := keyBinding) (issuance := issuance)
          (maxActions := maxActions) k)
      ⊆ sampledOrchardRelationEventUpTo spendAuthVerify bindingVerify issuance maxActions m gen v_idx r_idx
          queryOf toSig LA k := by
  rintro x ⟨hval, harm⟩
  refine ⟨hval, ?_⟩
  obtain ⟨i, hik, b, hb⟩ : ∃ i, i < k ∧ ∃ b, balanceSubsetOrBreak hval i = .inr b := by
    rcases harm with (⟨i, hik, b, hb, -⟩ | ⟨i, hik, b, hb, -⟩) | ⟨i, hik, b, hb, -⟩ <;>
      exact ⟨i, hik, b, hb⟩
  exact ⟨i, hik, kappaOrchardBalanceSubsetOrRelation_inr_of_break spendAuthVerify bindingVerify issuance
    maxActions m gen v_idx r_idx queryOf toSig x.2.1 x.2.2 hval i hb⟩

/-- **The Orchard Sinsemilla-relation event at a presented basis.** As
`sampledOrchardRelationEventUpTo`, over the coins and the challenge table alone: the output
ledger is valid at the presented basis's primitives and its data computes a nontrivial
discrete-log relation among the fixed Sinsemilla bases at some step `i < k`. -/
def orchardRelationEventUpToAt (basis : Fin m → PallasGroup) (k : ℕ) :
    Set (ι × (Q → Fq)) :=
  setOf fun x =>
    ∃ hval : ValidLedger (primitivesAtBasis m v_idx r_idx queryOf
        (primitives spendAuthVerify bindingVerify) toSig basis x.2) keyBinding issuance
        maxActions (((LA x.1 basis).run x.2).map Prod.fst),
      ∃ i, i < k ∧ ∃ rel, orchardBalanceSubsetOrRelationAtBasis spendAuthVerify bindingVerify
        issuance maxActions m v_idx r_idx queryOf toSig basis x.2 hval i = .inr rel

omit [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- **The three non-negativity arms collapse onto the Sinsemilla-relation event at a presented
basis.** As `sampledBalanceSubsetArms_subset_orchardRelation`, with the arm's break routed
through the basis-parametric Orchard reducer (`orchardBalanceSubsetOrRelationAtBasis`). -/
theorem balanceSubsetArmsAt_subset_orchardRelation (basis : Fin m → PallasGroup) (k : ℕ) :
    ledgerEventAt m v_idx r_idx queryOf (primitives spendAuthVerify bindingVerify) toSig basis LA
        (balanceSubsetArmsUpTo (kv := keyBinding) (issuance := issuance)
          (maxActions := maxActions) k)
      ⊆ orchardRelationEventUpToAt spendAuthVerify bindingVerify issuance maxActions m v_idx
          r_idx queryOf toSig LA basis k := by
  rintro x ⟨hval, harm⟩
  refine ⟨hval, ?_⟩
  obtain ⟨i, hik, b, hb⟩ : ∃ i, i < k ∧ ∃ b, balanceSubsetOrBreak hval i = .inr b := by
    rcases harm with (⟨i, hik, b, hb, -⟩ | ⟨i, hik, b, hb, -⟩) | ⟨i, hik, b, hb, -⟩ <;>
      exact ⟨i, hik, b, hb⟩
  exact ⟨i, hik, orchardBalanceSubsetOrRelationAtBasis_inr_of_break spendAuthVerify
    bindingVerify issuance maxActions m v_idx r_idx queryOf toSig basis x.2 hval i hb⟩

/-- **The Orchard integrity experiment for a KS-idealized adversary.** Over the idealized
adversary's coins, the challenge table, and the basis logs, the probability that the output
Orchard ledger is valid and violates balance integrity at some prefix `i < k` is at most
`ε_sinsemilladlr + (ε_dl + (qH+2)/#F)`. This is the abstract integrity experiment for an
idealized adversary with the non-negativity side discharged at the Orchard instantiation:
the three Balance-subset arms collapse onto the single advantage `ε_sinsemilladlr` of computing a
nontrivial Sinsemilla discrete-log relation (`sampledBalanceSubsetArms_subset_orchardRelation`),
replacing the abstract `ε_nonneg` with one term and no factor of three. The conservation side is
the abstract experiment's combined coin-consuming finder, so the whole bound carries one
discrete-log advantage per side: `ε_sinsemilladlr` among the fixed Sinsemilla bases, `ε_dl` at the
sampled value-commitment bases. -/
theorem orchardBalanceIntegrityBefore_measure_le_experiment_idealizedks (p : PMF ι)
    (hne_idx : v_idx ≠ r_idx)
    {qH : ℕ} (hQ : ∀ j basis, (LA j basis).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPoints m gen v_idx r_idx queryOf
      (primitives spendAuthVerify bindingVerify) toSig (LA j))
    (hr : maxActions * ((primitives spendAuthVerify bindingVerify).valueBound - 1)
        + (primitives spendAuthVerify bindingVerify).vBalanceBound
      < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD) (k : ℕ)
    {ε_sinsemilladlr ε_dl : ℝ≥0∞}
    (hsin : (challengeExperiment m p).toOuterMeasure
      (sampledOrchardRelationEventUpTo spendAuthVerify bindingVerify issuance maxActions m gen v_idx r_idx queryOf
        toSig LA k) ≤ ε_sinsemilladlr)
    (hdl : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen (fun basis table =>
      conservationRelFinder m v_idx r_idx queryOf (primitives spendAuthVerify bindingVerify) toSig hne_idx k
        (LA j) table basis) ε_dl) :
    (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf (primitives spendAuthVerify bindingVerify) toSig LA
          (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding) (issuance := issuance)
            (maxActions := maxActions) k))
      ≤ ε_sinsemilladlr + (ε_dl + ((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card Fq) :=
  balanceIntegrityBefore_measure_le_experiment m gen v_idx r_idx queryOf (primitives spendAuthVerify bindingVerify)
    toSig p hne_idx hQ halg hr k
    (le_trans (MeasureTheory.measure_mono
      (sampledBalanceSubsetArms_subset_orchardRelation spendAuthVerify bindingVerify issuance maxActions m gen
        v_idx r_idx queryOf toSig LA k)) hsin)
    hdl

end Zcash.Security.Ledger.Bridge

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Common Zcash.Security.BindingSignature Zcash.Security.RedDSA
open Zcash.Common.LabeledOracleComp
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Pool
open Zcash.Security.Ledger.Model
open scoped ENNReal

universe v

/-- The deployed challenge-query type: the literal triple the challenge hash consumes — the
signature's nonce `R`, the binding verification key `bvk`, and the sighash. Finite because
the Pallas group's affine representation is a computable finite enumeration. -/
abbrev OrchardQuery (MSG : Type v) : Type v := PallasGroup × PallasGroup × MSG

/-- The deployed challenge-query encoding: the identity triple. `queryOf`'s intended
injectivity (collisions only shrink the covered adversary class) is discharged here with no
collisions at all (`orchardQueryOf_injective`). -/
def orchardQueryOf {MSG : Type v} (R bvk : PallasGroup) (msg : MSG) : OrchardQuery MSG :=
  (R, bvk, msg)

/-- The identity triple is injective, so distinct binding-signature points query distinct
challenges. -/
theorem orchardQueryOf_injective {MSG : Type v} {R R' bvk bvk' : PallasGroup} {m m' : MSG}
    (h : orchardQueryOf R bvk m = orchardQueryOf R' bvk' m') :
    R = R' ∧ bvk = bvk' ∧ m = m' := by
  simpa [orchardQueryOf, Prod.ext_iff] using h

/-- The deployed discrete-log base: the standard Pallas generator. -/
def pallasGen : PallasGroup := ⟨CompElliptic.Curves.Pasta.Pallas.Gpt⟩

/-- The deployed discrete-log base is not the identity, so the textbook game at it is a
hardness claim rather than the degenerate zero-base game. -/
theorem pallasGen_ne_zero : pallasGen ≠ 0 := by decide

/-- The deployed value bases in the experiment's two slots: the value base 𝒱^Orchard and
the randomness base ℛ^Orchard. -/
def orchardValueBases : Fin 2 → PallasGroup := ![valueCommitV, valueCommitR]

/-- At the deployed value bases, the experiment's basis programming is invisible on the
value side: `primitivesAtBasis`'s value commitment is definitionally the deployed one.
Only `bindingVerify` differs — the challenge is read from the table instead of computed by
the challenge hash. -/
theorem primitivesAtBasis_orchardValueBases_valueCommit {MSG SIG : Type*}
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    (toSig : SIG → RedDSA.Sig Fq PallasGroup) {Q : Type} [DecidableEq Q]
    (queryOf : PallasGroup → PallasGroup → MSG → Q) (table : Q → Fq) :
    (primitivesAtBasis 2 0 1 queryOf (primitives spendAuthVerify bindingVerify) toSig
        orchardValueBases table).valueCommit
      = (primitives spendAuthVerify bindingVerify).valueCommit := rfl

/-- **The deployed KS-idealized balance adversary model, as a type.** This models the
adversary class of the deployed KS-idealized Balance experiments.

* `LA`: per coin, a labeled challenge-oracle machine from the presented bases to a
  **witness-annotated** ledger — every Action carries the witness for the Action statement,
  and each transaction its announced binding representation. The annotation is a stated
  **gap in the proof, not a modelling trade-off**: the composition with Halo 2
  knowledge soundness —extracting these witnesses from accepting proofs— is unproved
  (tracked in #147).
* `queryBound`: at most `qH` challenge-oracle queries — the random-oracle resource, priced
  in the bounds.
* `algebraic`: algebraic at the two binding-signature points (`AlgebraicAtBindingPoints`).

The sighash type `MSG` is opaque but finite — the challenge table is a finite object. The
spend-authorization predicate is arbitrary: Balance relies on no property of it, and in
particular does not need the sighash to commit to the transaction effects (Spendability and
Spend authority do). `H_bind` names the deployed binding challenge hash; the experiment
idealizes it as a random oracle (`IdealizedKSBalanceAdversary.violationEvent`). -/
structure IdealizedKSBalanceAdversary (MSG : Type) [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
    (spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop)
    (H_bind : PallasGroup → PallasGroup → MSG → Fq) : Type 1 where
  /-- The adversary's coin space. -/
  ι : Type
  /-- The coin distribution. -/
  coins : PMF ι
  /-- Per coin, the labeled challenge-oracle machine producing the witness-annotated
  ledger. -/
  LA : ι → (Fin 2 → PallasGroup) → LabeledOracleComp (OrchardQuery MSG) Fq
    (fun _ => QueryRep Fq 2)
    (List (Tx (KeyBinding.Pool.Witness Fq PallasGroup Fp) Fq PallasGroup Fp Fp Fp Encoding
      MSG (RedDSA.Sig Fq PallasGroup)
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)).depth × QueryRep Fq 2))
  /-- The challenge-oracle query budget. -/
  qH : ℕ
  /-- Every run stays within the budget. -/
  queryBound : ∀ j b, (LA j b).QueryBound qH
  /-- Algebraic at the binding-signature points, at every presented basis. The AGM reading
  makes no reference to how a presented basis was chosen, so the assumption is stated for
  all bases: the sampled experiments consume it at their sampled bases, and the deployed
  ones at `orchardValueBases`. -/
  algebraic : ∀ j : ι, ∀ basis, AlgebraicAtBindingPointsAt 2 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id basis (LA j)

namespace IdealizedKSBalanceAdversary

variable {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
  {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
  {H_bind : PallasGroup → PallasGroup → MSG → Fq}

/-- The sampled KS-idealized experiment's distribution: the adversary's coins, a uniform
challenge table, and uniform logs of the two presented bases. -/
noncomputable def experiment (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind) :
    PMF (A.ι × ((OrchardQuery MSG → Fq) × (Fin 2 → Fq))) :=
  challengeExperiment 2 A.coins

/-- **The sampled KS-idealized violation event.** The samples on which the adversary's
output ledger is valid at the sampled primitives and lands in the per-primitives event `E`.

The experiment's idealizations live here:

* Validity's `satisfied` conjunct reads the witness annotations that the adversary is
  required to provide. On the composed route this is discharged as data:
  `OrchardExtractionExperiment` builds the annotated adversary from a proof-emitting one,
  with the annotations computed by the Action-circuit extractors from the sampled runs,
  and its endpoints bound the deployed form of this event at the constructed adversary
  together with the extraction-failure arm. At a directly supplied adversary the
  annotations remain a modelling input.

The remaining idealizations are accepted as modelling trade-offs:

* The uniform challenge table is `H_bind` —the RedPallas binding challenge hash— modeled
  as a random oracle.
* Validity is at the sampled value and binding bases (`kappaPrimitivesAt`): the presented
  bases are random multiples of `pallasGen`, and the reference-string heuristic carries them
  to the deployed `𝒱^Orchard`, `ℛ^Orchard`.
* Byte encodings are elided, as at the RedDSA abstraction boundary. -/
def violationEvent (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind)
    (issuance : ℕ → ℕ) (maxActions : ℕ)
    (E : ∀ P : Primitives Fq PallasGroup Fp Fp Fp Fp Fp Encoding MSG
        (RedDSA.Sig Fq PallasGroup),
      Set (ValidAnnotated P keyBinding issuance maxActions)) :
    Set (A.ι × ((OrchardQuery MSG → Fq) × (Fin 2 → Fq))) :=
  sampledLedgerEvent 2 pallasGen 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id A.LA E

/-- The sampled Sinsemilla-relation event the non-negativity advantage is named on: the
deterministic reducer computes a nontrivial relation among the fixed Sinsemilla bases at
some prefix `i < k`. -/
def sinsemillaRelationEvent (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind)
    (issuance : ℕ → ℕ) (maxActions : ℕ) (k : ℕ) :
    Set (A.ι × ((OrchardQuery MSG → Fq) × (Fin 2 → Fq))) :=
  sampledOrchardRelationEventUpTo spendAuthVerify (redPallasBindingVerify H_bind) issuance
    maxActions 2 pallasGen 0 1 orchardQueryOf id A.LA k

/-- The deployed Sinsemilla-relation event the non-negativity advantage is named on, at the
deployed value bases: the deterministic reducer computes a nontrivial relation among the
fixed Sinsemilla bases at some prefix `i < k`. -/
def deployedSinsemillaRelationEvent
    (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind)
    (issuance : ℕ → ℕ) (maxActions : ℕ) (k : ℕ) :
    Set (A.ι × (OrchardQuery MSG → Fq)) :=
  orchardRelationEventUpToAt spendAuthVerify (redPallasBindingVerify H_bind) issuance
    maxActions 2 0 1 orchardQueryOf id A.LA orchardValueBases k

/-- The combined conservation finder the discrete-log advantage is stated for: replay coin
`j`'s machine once and return whichever arm's relation the sample yields. -/
def conservationFinder (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind) (k : ℕ)
    (j : A.ι) (basis : Fin 2 → PallasGroup) (table : OrchardQuery MSG → Fq) :
    Option (AlgebraicRelationWitness (F := Fq) basis) :=
  conservationRelFinder 2 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id (by decide) k (A.LA j)
      table basis

/-- The deployed fixed-basis experiment distribution: the adversary's coins and a uniform
challenge table. No basis logs are sampled. -/
noncomputable def deployedExperiment
    (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind) :
    PMF (A.ι × (OrchardQuery MSG → Fq)) :=
  challengeTableExperiment A.coins

/-- **The deployed violation event, at the deployed value bases.** The samples on which the
adversary's output ledger is valid at `primitivesAtBasis … orchardValueBases` and lands in
the per-primitives event `E`.

This is the form of the event that the composed extraction endpoints bound.

The idealizations are the sampled `violationEvent`'s, with two differences:

* No reference-string heuristic is involved: validity is at the deployed value bases.
  The value commitment at `orchardValueBases` is definitionally the deployed one
  (`primitivesAtBasis_orchardValueBases_valueCommit`), and only `bindingVerify` is
  replaced — the Schnorr equation with the challenge read from the table instead of
  computed by `H_bind`.
* On the composed route, the Fiat–Shamir transcript oracle is presented finitely, one
  independent table per bundle size (the `OrchardExtractionExperiment` module doc states
  why that presentation is sound). -/
def deployedViolationEvent (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind)
    (issuance : ℕ → ℕ) (maxActions : ℕ)
    (E : ∀ P : Primitives Fq PallasGroup Fp Fp Fp Fp Fp Encoding MSG
        (RedDSA.Sig Fq PallasGroup),
      Set (ValidAnnotated P keyBinding issuance maxActions)) :
    Set (A.ι × (OrchardQuery MSG → Fq)) :=
  ledgerEventAt 2 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id orchardValueBases A.LA E

/-- **The deployed value-DLR finder — the machine the named `ε_valuedlr` bounds.** Replay
coin `j`'s machine at the deployed value bases and return whichever arm's relation the
sample yields, as a nontrivial relation over the combined deployed basis, supported on
the two value slots. -/
def valueDLRFinder (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind) (k : ℕ)
    (j : A.ι) (table : OrchardQuery MSG → Fq) :
    Option (Zcash.NontrivialRelation (F := Fq) pallasS orchardPoints) :=
  (A.conservationFinder k j orchardValueBases table).map fun w =>
    w.embed ![Sum.inr .idxValueCommitV, Sum.inr .idxValueCommitR]
      (fun x => match x with
        | .inr .idxValueCommitV => some 0
        | .inr .idxValueCommitR => some 1
        | _ => none)
      (by
        intro x y
        rcases y with a | s
        · fin_cases x <;> simp
        · fin_cases x <;> cases s <;> decide)
      (fun i => by fin_cases i <;> rfl)

/-- The named-slot reindexing drops no sample: the combined finder's relation event at the
deployed value bases is the deployed finder's. -/
theorem conservationRelFiberAt_orchardValueBases
    (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind) (k : ℕ) (j : A.ι) :
    conservationRelFiberAt 2 0 1 orchardQueryOf
        (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id (by decide) k (A.LA j)
        orchardValueBases
      = {table | (A.valueDLRFinder k j table).isSome} := by
  ext table
  simp [conservationRelFiberAt, valueDLRFinder, conservationFinder]

end IdealizedKSBalanceAdversary

/-- **Balance integrity against a KS-idealized adversary for deployed Orchard.**
For every idealized balance adversary against the deployed Orchard protocol — a valid
output ledger violates balance integrity at some prefix `i < k` with probability at most
`ε_sinsemilladlr + (ε_dl + (qH+2)/#F)`.

The experiment's idealizations are described at `IdealizedKSBalanceAdversary.violationEvent`;
critically, they include idealizing knowledge soundness for the Action circuit verifier.
Connecting this up to the Action-circuit knowledge-soundness proof is tracked as #147.

The action cap `maxActions < 2^16` is the dedicated consensus rule on the action count —
`nActionsOrchard` and `nActionsIronwood` are each less than `2^16` (§7.1.2,
<https://zips.z.cash/protocol/protocol.pdf#txnconsensus>), so the result applies to either
Orchard-protocol pool. This is turned into no-overflow by `orchard_ledger_no_overflow`.

The two advantages are named bounds for exhibited machines, not hardness premisses. The
conservation side's is the combined finder's textbook discrete log. The non-negativity
side's is the discrete-log-relation advantage among the fixed Sinsemilla bases — one
tight programmed-basis step (Jaeger–Tessaro) above textbook discrete log, but this
experiment does not take that step; it programs only the value and binding bases. -/
theorem orchardBalanceIntegrity_measure_le_idealizedks
    {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
    {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
    {H_bind : PallasGroup → PallasGroup → MSG → Fq}
    (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind)
    (issuance : ℕ → ℕ) (maxActions : ℕ) (hmax : maxActions < 2^16) (k : ℕ)
    {ε_sinsemilladlr ε_dl : ℝ≥0∞}
    (hsin : A.experiment.toOuterMeasure (A.sinsemillaRelationEvent issuance maxActions k)
      ≤ ε_sinsemilladlr)
    (hdl : ∀ j : A.ι, TextbookDLWithCoinsAdvantageLE pallasGen (A.conservationFinder k j)
      ε_dl) :
    A.experiment.toOuterMeasure (A.violationEvent issuance maxActions
        (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding)
          (issuance := issuance) (maxActions := maxActions) k))
      ≤ ε_sinsemilladlr + (ε_dl + ((A.qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card Fq) :=
  orchardBalanceIntegrityBefore_measure_le_experiment_idealizedks spendAuthVerify
    (redPallasBindingVerify H_bind) issuance maxActions 2 pallasGen 0 1 orchardQueryOf id
    A.LA A.coins (by decide) A.queryBound (fun j logs => A.algebraic j (scalarBasis pallasGen logs))
    (orchard_ledger_no_overflow hmax) k
    hsin hdl

/-- **Balance conservation against a KS-idealized adversary for deployed Orchard.**
As for the idealized integrity endpoint (`orchardBalanceIntegrity_measure_le_idealizedks`),
covering the conservation violation alone: the bound is the conservation side's
`ε_dl + (qH+2)/#F`. The model and idealizations are `IdealizedKSBalanceAdversary` and its
`violationEvent`. -/
theorem orchardBalanceConservation_measure_le_idealizedks
    {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
    {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
    {H_bind : PallasGroup → PallasGroup → MSG → Fq}
    (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind)
    (issuance : ℕ → ℕ) (maxActions : ℕ) (hmax : maxActions < 2^16) (k : ℕ)
    {ε_dl : ℝ≥0∞}
    (hdl : ∀ j : A.ι, TextbookDLWithCoinsAdvantageLE pallasGen (A.conservationFinder k j)
      ε_dl) :
    A.experiment.toOuterMeasure (A.violationEvent issuance maxActions
        (fun P => balanceConservationViolationBefore (P := P) (kv := keyBinding)
          (issuance := issuance) (maxActions := maxActions) k))
      ≤ ε_dl + ((A.qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card Fq :=
  balanceConservationBefore_measure_le_experiment 2 pallasGen 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
    (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
    A.coins (by decide) A.queryBound (fun j logs => A.algebraic j (scalarBasis pallasGen logs))
    (orchard_ledger_no_overflow hmax) k hdl

/-- **Shielded balance cap against a KS-idealized adversary for deployed Orchard.**
As the idealized conservation endpoint, for the shielded pool exceeding the minted issuance
at some prefix `i < k`. The model and idealizations are `IdealizedKSBalanceAdversary` and its
`violationEvent`. -/
theorem orchardShieldedBalanceCap_measure_le_idealizedks
    {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
    {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
    {H_bind : PallasGroup → PallasGroup → MSG → Fq}
    (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind)
    (issuance : ℕ → ℕ) (maxActions : ℕ) (hmax : maxActions < 2^16) (k : ℕ)
    {ε_dl : ℝ≥0∞}
    (hdl : ∀ j : A.ι, TextbookDLWithCoinsAdvantageLE pallasGen (A.conservationFinder k j)
      ε_dl) :
    A.experiment.toOuterMeasure (A.violationEvent issuance maxActions
        (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := keyBinding)
          (issuance := issuance) (maxActions := maxActions) k))
      ≤ ε_dl + ((A.qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card Fq :=
  shieldedBalanceCapBefore_measure_le_experiment 2 pallasGen 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
    (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
    A.coins (by decide) A.queryBound (fun j logs => A.algebraic j (scalarBasis pallasGen logs))
    (orchard_ledger_no_overflow hmax) k hdl

/-- **Balance conservation against a KS-idealized adversary, at the deployed value bases.**
For every idealized balance adversary against the deployed Orchard protocol, a valid output
ledger violates balance conservation at some prefix `i < k` with probability at most
`ε_valuedlr + (qH+1)/#F` over the coins and the challenge table. No basis is sampled:
validity is at the deployed value bases (`deployedViolationEvent`), and `ε_valuedlr` is the
named advantage of the exhibited deployed finder (`valueDLRFinder`) — the probability that
it returns a nontrivial relation over the named 𝒱/ℛ slots. The idealizations are
`deployedViolationEvent`'s; the action cap is as at the sampled endpoints
(`orchardBalanceIntegrity_measure_le_idealizedks`). -/
theorem orchardBalanceConservation_measure_le_idealizedks_deployed
    {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
    {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
    {H_bind : PallasGroup → PallasGroup → MSG → Fq}
    (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind)
    (issuance : ℕ → ℕ) (maxActions : ℕ) (hmax : maxActions < 2^16) (k : ℕ)
    {ε_valuedlr : ℝ≥0∞}
    (hrel : ∀ j : A.ι, (PMF.uniformOfFintype (OrchardQuery MSG → Fq)).toOuterMeasure
        {table | (A.valueDLRFinder k j table).isSome} ≤ ε_valuedlr) :
    A.deployedExperiment.toOuterMeasure (A.deployedViolationEvent issuance maxActions
        (fun P => balanceConservationViolationBefore (P := P) (kv := keyBinding)
          (issuance := issuance) (maxActions := maxActions) k))
      ≤ ε_valuedlr + ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq :=
  balanceConservationBefore_measure_le_experimentAt 2 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
    (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
    A.coins (basis := orchardValueBases) (by decide) (fun j => A.queryBound j _)
    (fun j => A.algebraic j orchardValueBases) (orchard_ledger_no_overflow hmax) k
    (fun j => by
      rw [A.conservationRelFiberAt_orchardValueBases k j]
      exact hrel j)

/-- **Shielded balance cap against a KS-idealized adversary, at the deployed value bases.**
As the deployed conservation endpoint
(`orchardBalanceConservation_measure_le_idealizedks_deployed`), for the shielded pool
exceeding the minted issuance at some prefix `i < k`. -/
theorem orchardShieldedBalanceCap_measure_le_idealizedks_deployed
    {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
    {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
    {H_bind : PallasGroup → PallasGroup → MSG → Fq}
    (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind)
    (issuance : ℕ → ℕ) (maxActions : ℕ) (hmax : maxActions < 2^16) (k : ℕ)
    {ε_valuedlr : ℝ≥0∞}
    (hrel : ∀ j : A.ι, (PMF.uniformOfFintype (OrchardQuery MSG → Fq)).toOuterMeasure
        {table | (A.valueDLRFinder k j table).isSome} ≤ ε_valuedlr) :
    A.deployedExperiment.toOuterMeasure (A.deployedViolationEvent issuance maxActions
        (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := keyBinding)
          (issuance := issuance) (maxActions := maxActions) k))
      ≤ ε_valuedlr + ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq :=
  shieldedBalanceCapBefore_measure_le_experimentAt 2 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
    (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
    A.coins (basis := orchardValueBases) (by decide) (fun j => A.queryBound j _)
    (fun j => A.algebraic j orchardValueBases) (orchard_ledger_no_overflow hmax) k
    (fun j => by
      rw [A.conservationRelFiberAt_orchardValueBases k j]
      exact hrel j)

/-- **Balance integrity against a KS-idealized adversary, at the deployed value bases.**
As the sampled endpoint (`orchardBalanceIntegrity_measure_le_idealizedks`), over the coins
and the challenge table alone, at `ε_sinsemilladlr + (ε_valuedlr + (qH+1)/#F)`. No basis is
sampled: validity is at the deployed value bases, the non-negativity side is the deployed
Sinsemilla-relation advantage (`deployedSinsemillaRelationEvent`), and the conservation
side's relation arm is the named `ε_valuedlr` for the exhibited deployed finder
(`valueDLRFinder`). The idealizations are `deployedViolationEvent`'s. -/
theorem orchardBalanceIntegrity_measure_le_idealizedks_deployed
    {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
    {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
    {H_bind : PallasGroup → PallasGroup → MSG → Fq}
    (A : IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind)
    (issuance : ℕ → ℕ) (maxActions : ℕ) (hmax : maxActions < 2^16) (k : ℕ)
    {ε_sinsemilladlr ε_valuedlr : ℝ≥0∞}
    (hsin : A.deployedExperiment.toOuterMeasure
      (A.deployedSinsemillaRelationEvent issuance maxActions k) ≤ ε_sinsemilladlr)
    (hrel : ∀ j : A.ι, (PMF.uniformOfFintype (OrchardQuery MSG → Fq)).toOuterMeasure
        {table | (A.valueDLRFinder k j table).isSome} ≤ ε_valuedlr) :
    A.deployedExperiment.toOuterMeasure (A.deployedViolationEvent issuance maxActions
        (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding)
          (issuance := issuance) (maxActions := maxActions) k))
      ≤ ε_sinsemilladlr + (ε_valuedlr + ((A.qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card Fq) :=
  balanceIntegrityBefore_measure_le_experimentAt 2 0 1 orchardQueryOf
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
    (kv := keyBinding) (issuance := issuance) (maxActions := maxActions)
    A.coins (basis := orchardValueBases) (by decide) (fun j => A.queryBound j _)
    (fun j => A.algebraic j orchardValueBases) (orchard_ledger_no_overflow hmax) k
    (le_trans (MeasureTheory.measure_mono
      (balanceSubsetArmsAt_subset_orchardRelation spendAuthVerify
        (redPallasBindingVerify H_bind) issuance maxActions 2 0 1 orchardQueryOf id A.LA
        orchardValueBases k)) hsin)
    (fun j => by
      rw [A.conservationRelFiberAt_orchardValueBases k j]
      exact hrel j)

end Zcash.Security.Ledger.Bridge
