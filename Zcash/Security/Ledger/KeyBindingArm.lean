import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.KeyBinding.Instance
import Zcash.Security.Ledger.Balance
import Zcash.Security.Ledger.SpendAuthority

-- This lint enforces Mathlib's minimal-hypothesis style, from which we deliberately depart.
set_option linter.unusedSectionVars false

/-!
# The key-binding arm's ε, discharged in the oracle model

The capstone layer bounds each game's break arms by named ε hypotheses. This module
bounds the key-binding arms in the key-binding oracle model at the reductions' own
events: `(n + 4) · (n + 3) / |RIVK|` for any `n`-query-bounded adversary — the bound
of `toInterface_break_measure_le`, inherited at an unchanged query count because
recovering the arm's witness pair makes no oracle queries.

The adversary outputs a ledger; it cannot run the reduction itself, because
`balanceSubsetOrBreak` consumes a validity proof whose meaning depends on the sampled
oracle (through the sampled interface `kvAt`) and an oracle machine's result type
cannot depend on the table it is run against. But the machine does not need to: the
arm's witness pair is an oracle-free function of the ledger. For Balance it is
`kbPairOf` — the duplicate positioned opening `findPair` locates, projected to its
key witnesses — and `balanceSubsetOrBreak_kbPair` identifies it with the pair of
whatever break the reduction computes, so the bounded event is simply "the reduction
lands in the key-binding arm". The composite machine returning the pair is covered by
the key-binding bound, and validity lives only inside the event.

Spend Authority's arm differs in one respect: its selection criterion includes the
undecidable `¬ Signed`, so no computable scan can locate the offending action. The
adversary therefore announces a transaction and action index alongside its ledger —
pointing at its own break, as is standard in security games — and the machine reads
the first witness off the announced indices (`kwAt`, oracle-free) with the victim
`wV` as the second. `spendAuthorityOrBreak_pair` identifies the reduction's pair with
that output, and the event is the bundled `SpendAuthorityKBArm` at the announced
indices.
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Security.KeyBinding Zcash.Snark

-- A shared universe for the oracle-model types, so the sampling experiment can be
-- written in `do`-notation: `PMF`'s monad instance fixes one universe for the whole
-- block, which the independent `Type*` universes could not satisfy.
universe u
variable {G IVK AK NK RIVK ASK QK SK : Type u}
variable {RHO PSI MHASH MENC MSG SIG : Type*}

section OracleModel

variable [AddCommGroup G] [Field IVK] [Field RIVK] [Module RIVK G]
  [NoZeroSMulDivisors RIVK G] [SMul ASK G]
  [Fintype AK] [Fintype NK] [Fintype RIVK] [Fintype ASK] [Fintype QK] [Fintype SK]
  [Nonempty NK] [Nonempty ASK]
  [DecidableEq AK] [DecidableEq NK] [DecidableEq RIVK] [DecidableEq QK] [DecidableEq SK]
  [DecidableEq G] [DecidableEq RHO] [DecidableEq PSI] [DecidableEq MHASH]
  [DecidableEq MENC]

/-- The games-facing key-binding interface at a sampled oracle assignment: the two
sampled key tables plus the three components of the combined `rivk` oracle. -/
abbrev kvAt (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G)
    (Hask : SK → ASK) (Hnk : SK → NK) (O : FinalQuery AK NK RIVK QK SK → RIVK) :
    KeyBindingInterface (KeyBinding.Witness G IVK AK NK RIVK QK SK) G IVK NK :=
  KeyBinding.toInterface Extract S hfn Ggen
    ⟨Hask, Hnk, fun sk => O (.legacy sk),
      fun qk ak nk => O (.ext qk ak nk),
      fun rivk_ext ak nk => O (.int rivk_ext ak nk)⟩

/-- **The key-binding arm's ε, discharged.** For any `n`-query-bounded ledger adversary
in the key-binding oracle model, the probability that its output ledger is valid and the
Balance-subset reduction lands in the key-binding arm is at most
`(n + 4) · (n + 3) / |RIVK|`. The adversary outputs only a ledger; the arm's witness pair
is recovered from that ledger by the oracle-free `kbPairOf` (`balanceSubsetOrBreak_kbPair`
identifies it with the reduction's own pair), so the composite that returns the pair makes
no queries beyond the adversary's own and `toInterface_break_measure_le` applies unchanged.
`kbPairOf` is `Option`-valued (`findPair` may find no duplicate) while the bound's machine
must return a concrete pair, so the composite collapses it with `Option.getD default`; the
default is furnished by `[Inhabited (Witness …)]`, present at the concrete instantiation. On
every sample of the bounded event `kbPairOf` is `some`, so the default is never used. -/
theorem balanceSubset_keyBindingArm_measure_le {ι : Type u}
    [Inhabited (KeyBinding.Witness G IVK AK NK RIVK QK SK)]
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G) (hS : S ≠ 0)
    (p : PMF ι)
    (P : Primitives RIVK G IVK NK RHO PSI MHASH MENC MSG SIG)
    (issuance : ℕ → ℕ) (maxActions : ℕ) (i : ℕ)
    {LA : ι → (SK → ASK) → (SK → NK) →
      OracleComp (FinalQuery AK NK RIVK QK SK) RIVK
        (Ledger (KeyBinding.Witness G IVK AK NK RIVK QK SK) RIVK G RHO PSI MHASH MENC
            MSG SIG P.depth)}
    {n : ℕ} (hQ : ∀ j Hask Hnk, (LA j Hask Hnk).QueryBound n) :
    ((kbExperiment p)).toOuterMeasure
        (setOf fun (j, Hask, Hnk, O) =>
          ∃ hval : ValidLedger P (kvAt Extract S hfn Ggen Hask Hnk O)
              issuance maxActions ((LA j Hask Hnk).run O),
            ∃ w₁ w₂ h, balanceSubsetOrBreak hval i
              = PSum.inr (BalanceBreak.keyBinding w₁ w₂ h))
      ≤ ((n + 4) * (n + 3) : ℕ) / Fintype.card RIVK := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (toInterface_break_measure_le Extract S hfn Ggen hS p
      (A := fun j Hask Hnk => (LA j Hask Hnk).bind fun L => .pure ((kbPairOf L i).getD default))
      (n := n) (fun j Hask Hnk => ?_))
  · rintro ⟨j, Hask, Hnk, O⟩ ⟨hval, w₁, w₂, h, heq⟩
    simp only [Set.mem_setOf_eq, OracleComp.run_bind, OracleComp.run_pure]
    have hkp : kbPairOf ((LA j Hask Hnk).run O) i = some (w₁, w₂) := by
      have := balanceSubsetOrBreak_kbPair hval i heq
      simpa [BalanceBreak.kbPair] using this.symm
    rw [hkp]
    exact h
  · exact OracleComp.queryBound_bind (hQ j Hask Hnk)
      fun L => OracleComp.QueryBound.pure _ 0

/-- **The Spend Authority key-binding arm's ε, discharged.** For any `n`-query-bounded
ledger adversary in the key-binding oracle model that announces its ledger together with
a transaction and action index — pointing at its own break, as is standard in security
games — the probability that the ledger is valid and the Spend Authority reduction, at
the announced action spending a note addressed to the victim `wV` over an unsigned
sighash, lands in the key-binding arm is at most `(n + 4) · (n + 3) / |RIVK|`. The
indices are announced because the arm's selection criterion includes the undecidable
`¬ Signed`, so no computable scan can locate the action the way `kbPairOf` does for
Balance; the arm's pair is still derived, never announced — `kwAt` reads the first
witness off the announced indices (oracle-free) and `spendAuthorityOrBreak_pair`
identifies the reduction's pair with `(kwAt …, wV)`. -/
theorem spendAuthority_keyBindingArm_measure_le {ι : Type u}
    [Inhabited (KeyBinding.Witness G IVK AK NK RIVK QK SK)]
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G) (hS : S ≠ 0)
    (p : PMF ι)
    (P : Primitives RIVK G IVK NK RHO PSI MHASH MENC MSG SIG)
    (issuance : ℕ → ℕ) (maxActions : ℕ)
    (wV : KeyBinding.Witness G IVK AK NK RIVK QK SK) (Signed : MSG → Prop)
    {LA : ι → (SK → ASK) → (SK → NK) →
      OracleComp (FinalQuery AK NK RIVK QK SK) RIVK
        (Ledger (KeyBinding.Witness G IVK AK NK RIVK QK SK) RIVK G RHO PSI MHASH MENC
            MSG SIG P.depth
          × ℕ × ℕ)}
    {n : ℕ} (hQ : ∀ j Hask Hnk, (LA j Hask Hnk).QueryBound n) :
    ((kbExperiment p)).toOuterMeasure
        (setOf fun (j, Hask, Hnk, O) =>
          Nonempty (SpendAuthorityKBArm P (kvAt Extract S hfn Ggen Hask Hnk O)
            issuance maxActions ((LA j Hask Hnk).run O).1
            ((LA j Hask Hnk).run O).2.1 ((LA j Hask Hnk).run O).2.2 wV Signed))
      ≤ ((n + 4) * (n + 3) : ℕ) / Fintype.card RIVK := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (toInterface_break_measure_le Extract S hfn Ggen hS p
      (A := fun j Hask Hnk => (LA j Hask Hnk).bind fun out =>
        .pure ((kwAt out.1 out.2.1 out.2.2).getD default, wV))
      (n := n) (fun j Hask Hnk => ?_))
  · rintro ⟨j, Hask, Hnk, O⟩ ⟨hf⟩
    simp only [Set.mem_setOf_eq, OracleComp.run_bind, OracleComp.run_pure]
    obtain ⟨hw₁, hw₂⟩ :=
      spendAuthorityOrBreak_pair hf.hval _ _ hf.hKB hf.hrecv hf.hfresh hf.hb
    have hkw : kwAt ((LA j Hask Hnk).run O).1 ((LA j Hask Hnk).run O).2.1
        ((LA j Hask Hnk).run O).2.2 = some hf.a.w.kw := by
      simp [kwAt, hf.htx, hf.ha]
    rw [hkw]
    simpa [hw₁, hw₂] using hf.b.h
  · exact OracleComp.queryBound_bind (hQ j Hask Hnk)
      fun out => OracleComp.QueryBound.pure _ 0

end OracleModel

end Zcash.Security.Ledger.Model
