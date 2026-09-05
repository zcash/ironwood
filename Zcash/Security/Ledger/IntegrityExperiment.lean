import Zcash.Common.Oracle.LabeledOracleComp
import Zcash.Security.Ledger.ConservationExperiment
import Zcash.Security.Ledger.Capstone

/-!
# The integrity experiment: the non-negativity and conservation arms in one sample space

The `BalanceIntegrity` capstone bounds an integrity violation by
`ε_merkle + ε_nc + ε_kb + ε_conservation`, over an abstract `PMF (ValidAnnotated …)`, with
each arm's bound a named hypothesis (`balanceIntegrity_measure_le`). A violation is the
shielded pool going negative, or the pools failing to sum to the minted issuance, at some
prefix `i < k`. This module places that composition in the challenge-oracle model, over the
*same* sample space as the conservation experiment: the adversary's coins, the challenge
table, and the logs of the `m` presented bases.

The reduction layer is what lets the two sides share one sample space. The conservation side
runs on the sampled value and binding bases (`kappaPrimitivesAt`; the `kappa` prefix names the
knowledge-error analysis that these sampled forms serve) and is discharged wholesale by
the conservation experiment: one combined coin-consuming finder covering both of its arms'
relation slices, at `ε_dl + (qH+2)/#F`. The non-negativity side's three arms (Merkle,
note-commitment, key-binding) are deterministic reductions to breaks among primitives that
`kappaPrimitivesAt` leaves fixed, so they do not add a sample-space dimension: the experiment
takes their union as one named bound `ε_nonneg` over this same space. At the Orchard instantiation
that collapses to the single Sinsemilla discrete-log-relation advantage.

The composition is the capstone layer's own per-primitives containment
(`balanceIntegrityViolationBefore_subset_conservation`): at each sample a violation lands in one
of the three non-negativity arms or in the conservation violation itself. That set-level
containment lifts to the sample space through the `sampledLedgerEvent` join-homomorphism
(`sampledBalanceIntegrity_subset`, which is monotone and preserves unions), and a union bound
over the two lifted events gives `ε_nonneg + (ε_dl + (qH+2)/#F)`, with no factor of `k`.

Two abstractions keep the statements readable: `challengeExperiment` is the sample distribution,
and `sampledLedgerEvent` lifts a per-primitives ledger event to the samples on which the output
ledger is valid at the sampled primitives and lands in it — a monotone join-homomorphism, which
is what makes the containment lift in one step.
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Common Zcash.Security.BindingSignature Zcash.Security.RedDSA Zcash.Snark
open Zcash.Common.LabeledOracleComp
open scoped ENNReal

universe u

variable {r : ℕ} [Fact (Nat.Prime r)]
variable {G : Type*} [AddCommGroup G] [Module (ZMod r) G] [DecidableEq G]
  [NoZeroSMulDivisors (ZMod r) G]
variable {Q : Type u} [Fintype Q] [DecidableEq Q] [Inhabited Q]
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}
  [DecidableEq RHO] [DecidableEq PSI] [DecidableEq MHASH] [DecidableEq MENC] [DecidableEq NK]
variable (m : ℕ)

variable (gen : G) (v_idx r_idx : Fin m) (queryOf : G → G → MSG → Q)
  (P₀ : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG)
  (toSig : SIG → RedDSA.Sig (ZMod r) G)
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- The combined non-negativity arm event at primitives `P`: a Merkle, note-commitment, or
key-binding Balance-subset break at some prefix `i < k`. The integrity experiments take one
named bound (`ε_nonneg`) on the lift of this family. -/
def balanceSubsetArmsUpTo (k : ℕ)
    (P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  balanceSubsetBreakEventUpTo (P := P) (kv := kv) (issuance := issuance)
      (maxActions := maxActions) k .merkle
    ∪ balanceSubsetBreakEventUpTo (P := P) (kv := kv) (issuance := issuance)
      (maxActions := maxActions) k .noteCommit
    ∪ balanceSubsetBreakEventUpTo (P := P) (kv := kv) (issuance := issuance)
      (maxActions := maxActions) k .keyBinding

omit [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- **The challenge-experiment integrity containment.** The samples on which the output ledger
is valid and violates balance integrity are contained in the lift of the union of the three
non-negativity arms —Merkle, note-commitment, key-binding— together with the lifted
conservation violation. This is the capstone layer's per-primitives
`balanceIntegrityViolationBefore_subset_conservation` lifted through the `sampledLedgerEvent`
join-homomorphism (`sampledLedgerEvent_mono` then `sampledLedgerEvent_union`). -/
theorem sampledBalanceIntegrity_subset {ι : Type u}
    (LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (k : ℕ) :
    sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
        (fun P => balanceIntegrityViolationBefore (P := P) (kv := kv) (issuance := issuance)
          (maxActions := maxActions) k)
      ⊆ sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (balanceSubsetArmsUpTo (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k)
        ∪ sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (fun P => balanceConservationViolationBefore (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k) :=
  (sampledLedgerEvent_mono m gen v_idx r_idx queryOf P₀ toSig LA
    fun P => balanceIntegrityViolationBefore_subset_conservation (P := P) (kv := kv)
      (issuance := issuance) (maxActions := maxActions) k).trans
    (sampledLedgerEvent_union m gen v_idx r_idx queryOf P₀ toSig LA
      _
      (fun P => balanceConservationViolationBefore (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) k)).le

/-- **The integrity experiment.** Over the adversary's coins, the challenge table, and the
basis logs, the probability that the output ledger is valid and violates balance integrity at
some prefix `i < k`, at the sampled primitives, is at most `ε_nonneg + (ε_dl + (qH+2)/#F)`.
A violation is the shielded pool going negative, or the pools failing to sum to the minted
issuance. The non-negativity side is one named bound on the combined arm event over this same
space; the conservation side is the combined coin-consuming finder's discrete-log bound. -/
theorem balanceIntegrityBefore_measure_le_experiment {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    (hne_idx : v_idx ≠ r_idx)
    {qH : ℕ} (hQ : ∀ j basis, (LA j basis).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPoints m gen v_idx r_idx queryOf P₀ toSig (LA j))
    (hr : maxActions * (P₀.valueBound - 1) + P₀.vBalanceBound < r) (k : ℕ) {ε_nonneg ε_dl : ℝ≥0∞}
    (hnn : (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (balanceSubsetArmsUpTo (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k)) ≤ ε_nonneg)
    (hdl : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen (fun basis table =>
      conservationRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) table basis) ε_dl) :
    (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (fun P => balanceIntegrityViolationBefore (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k))
      ≤ ε_nonneg + (ε_dl + ((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r)) := by
  have hcons := balanceConservationBefore_measure_le_experiment m gen v_idx r_idx queryOf P₀
    toSig (kv := kv) (issuance := issuance) (maxActions := maxActions)
    p hne_idx hQ halg hr k hdl
  exact le_trans
    (toOuterMeasure_le_add₂ _
      (sampledBalanceIntegrity_subset m gen v_idx r_idx queryOf P₀ toSig LA k))
    (add_le_add hnn hcons)

omit [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- **The integrity containment at a fixed basis.** As `sampledBalanceIntegrity_subset`,
lifted through the `ledgerEventAt` join-homomorphism at the presented `basis`. -/
theorem balanceIntegrityAt_subset {ι : Type u} (basis : Fin m → G)
    (LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (k : ℕ) :
    ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA
        (fun P => balanceIntegrityViolationBefore (P := P) (kv := kv) (issuance := issuance)
          (maxActions := maxActions) k)
      ⊆ ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA
          (balanceSubsetArmsUpTo (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k)
        ∪ ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA
          (fun P => balanceConservationViolationBefore (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k) :=
  (ledgerEventAt_mono m v_idx r_idx queryOf P₀ toSig basis LA
    fun P => balanceIntegrityViolationBefore_subset_conservation (P := P) (kv := kv)
      (issuance := issuance) (maxActions := maxActions) k).trans
    (ledgerEventAt_union m v_idx r_idx queryOf P₀ toSig basis LA
      _
      (fun P => balanceConservationViolationBefore (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) k)).le

/-- **The integrity experiment at a fixed basis.** Over the adversary's coins and the
challenge table alone, at the presented `basis`, the probability that the output ledger is
valid and violates balance integrity at some prefix `i < k` is at most
`ε_nonneg + (ε_valuedlr + (qH+1)/#F)`. The non-negativity side is one named bound on the
combined arm event over this same space; the conservation side is the fixed-basis
conservation experiment, with its relation arm the named per-coin hypothesis `hrel`. -/
theorem balanceIntegrityBefore_measure_le_experimentAt {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {basis : Fin m → G} (hne_idx : v_idx ≠ r_idx)
    {qH : ℕ} (hQ : ∀ j, (LA j basis).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPointsAt m v_idx r_idx queryOf P₀ toSig basis (LA j))
    (hr : maxActions * (P₀.valueBound - 1) + P₀.vBalanceBound < r) (k : ℕ)
    {ε_nonneg ε_valuedlr : ℝ≥0∞}
    (hnn : (challengeTableExperiment p).toOuterMeasure
        (ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA
          (balanceSubsetArmsUpTo (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k)) ≤ ε_nonneg)
    (hrel : ∀ j : ι, (PMF.uniformOfFintype (Q → ZMod r)).toOuterMeasure
        (conservationRelFiberAt m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) basis)
      ≤ ε_valuedlr) :
    (challengeTableExperiment p).toOuterMeasure
        (ledgerEventAt m v_idx r_idx queryOf P₀ toSig basis LA
          (fun P => balanceIntegrityViolationBefore (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k))
      ≤ ε_nonneg + (ε_valuedlr + ((qH + 1 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r)) := by
  have hcons := balanceConservationBefore_measure_le_experimentAt m v_idx r_idx queryOf P₀
    toSig (kv := kv) (issuance := issuance) (maxActions := maxActions)
    p hne_idx hQ halg hr k hrel
  exact le_trans
    (toOuterMeasure_le_add₂ _
      (balanceIntegrityAt_subset m v_idx r_idx queryOf P₀ toSig basis LA k))
    (add_le_add hnn hcons)

end Zcash.Security.Ledger.Model
