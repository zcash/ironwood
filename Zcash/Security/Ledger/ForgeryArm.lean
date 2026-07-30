import Mathlib.Tactic
import Mathlib.Probability.Distributions.Uniform
import Zcash.Security.Ledger.Capstone
import Zcash.Security.RedDSA.SURK

-- This lint enforces Mathlib's minimal-hypothesis style, from which we deliberately depart.
set_option linter.unusedSectionVars false

/-!
# The Spend Authority forgery arm, against SURK-CMA

The capstone `spendAuthority_measure_le` bounds the Spend Authority violation by the
forgery arm's ε plus the key-binding arm's ε. This module gives the forgery arm's ε
its honest name: with the model's signature primitives pinned to RedDSA
(`SpendAuthShape`), every sample on which the reduction lands in the forgery arm
exhibits a SURK-CMA win — against the victim's `akP wV` or against `−akP wV`,
according to the forgery's `negated` flag — so the arm's ε is the adversary's
SURK-CMA advantage at those two keys, and nothing else.

* `SpendAuthShape` pins `Primitives.spendAuthVerify` and `Primitives.randomizePublic`
  to an abstract RedDSA scheme (`Zcash.Security.RedDSA.Basic`), the way `ValueShape`
  pins `valueCommit` to the Pedersen shape. The bases stay abstract; the concrete
  RedPallas instantiation is deferred, per the abstract-route plan.
* `SpendAuthForgery.toSURKWin` is the deterministic reduction: a forgery *is* a win
  (`Zcash.Security.RedDSA.SURK`), its message-level freshness discharging the game's
  pair-level clause a fortiori, given that every transcript message lies in `Signed`.
* The forgery event splits by sign (`spendAuthorityForgeryArmEvent`), each half
  yielding a win against its key (`spendAuthorityForgeryArm_win`), and the capstone
  composes with the two named bounds summed (`spendAuthority_measure_le_surk`) — the
  design's accepted factor-of-2: the circuit pins `ak^ℙ` only up to y-sign, so the
  hypothesis must cover `akV` and `−akV` (see the module doc of
  `Zcash.Security.Ledger.SpendAuthority`).

What stays named: SURK-CMA of RedDSA itself — the bound on the probability that an
adversary interacting with the signing oracle exhibits a `SURKWin`. The two ε
hypotheses consumed here are exactly that bound at the two keys; the oracle-machine
model connecting a ledger adversary to the game's transcript (the analogue of
`KeyBindingArm`'s `kbExperiment`) is tracked in #155, as it is for the key-binding
arm's own named-ε slot (see the module doc of `Zcash.Security.Ledger.Capstone`).
-/

namespace Zcash.Security.Ledger.Model

open scoped ENNReal

variable {F : Type*}
variable {G : Type*}
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}

section Validity

variable [Field F] [AddCommGroup G] [Module F G]
variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- The RedDSA shape of the spend-authorization primitives: an abstract scheme whose
verification equation and public-key randomization are what `spendAuthVerify` and
`randomizePublic` compute, with `toSig` decoding the model's opaque signature type.
The counterpart of `ValueShape` for the signature side. -/
structure SpendAuthShape (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG) where
  sch : RedDSA.Scheme F G MSG
  toSig : SIG → RedDSA.Sig F G
  verify_iff : ∀ (rk : G) (m : MSG) (σ : SIG),
    P.spendAuthVerify rk m σ ↔ sch.Verify rk m (toSig σ)
  randomize_eq : ∀ (α : F) (k : G), P.randomizePublic α k = sch.randomizePublic α k

/-- **A spend-authorization forgery is a SURK-CMA win.** Under the RedDSA shape, a
`SpendAuthForgery` against `akV` yields a `SURKWin` against `akV` or `−akV` as its
`negated` flag directs, judged against any transcript whose messages all lie in
`Signed`: the forgery's `rk` is the α-randomization of the target key, its signature
verifies there, and its message-level freshness gives the game's pair-level clause a
fortiori. -/
def SpendAuthForgery.toSURKWin (S : SpendAuthShape P) {akV : G} {Signed : MSG → Prop}
    (f : SpendAuthForgery P akV Signed)
    (hist : List (RedDSA.SigningAnswer F G MSG))
    (hhist : ∀ q ∈ hist, Signed q.m) :
    RedDSA.SURKWin S.sch (cond f.negated (-akV) akV) hist :=
  RedDSA.SURKWin.ofMessageFresh f.msg (S.toSig f.sig) f.α
    (by rw [← S.randomize_eq, ← f.rk_eq]; exact (S.verify_iff _ _ _).mp f.verifies)
    hhist f.fresh

section Arm

variable [DecidableEq G] [NoZeroSMulDivisors F G]

/-- The forgery arm event, split by the forgery's sign: the samples of
`spendAuthorityForgeryEvent` on which the computed forgery's `negated` flag is `neg` —
so the target key is `akP wV` at `neg = false` and `−akP wV` at `neg = true`. -/
def spendAuthorityForgeryArmEvent (wV : KW) (hKB : kv.KB wV) (Signed : MSG → Prop)
    (neg : Bool) : Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ tx, ∃ htx : tx ∈ ω.1, ∃ a, ∃ ha : a ∈ tx.actions,
    ∃ hrecv : a.w.note_old.pkd = P.emb (kv.ivk wV) • a.w.note_old.gd,
    ∃ hfresh : ¬ Signed tx.sighash, ∃ f,
    spendAuthorityOrBreak ω.2 htx ha hKB hrecv hfresh = .inl f ∧ f.negated = neg}

/-- The forgery event is covered by its two sign-split halves. -/
theorem spendAuthorityForgeryEvent_subset (wV : KW) (hKB : kv.KB wV)
    (Signed : MSG → Prop) :
    spendAuthorityForgeryEvent (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) wV hKB Signed
      ⊆ spendAuthorityForgeryArmEvent wV hKB Signed false
        ∪ spendAuthorityForgeryArmEvent wV hKB Signed true := by
  rintro ω ⟨tx, htx, a, ha, hrecv, hfresh, f, hf⟩
  cases hneg : f.negated
  · exact Or.inl ⟨tx, htx, a, ha, hrecv, hfresh, f, hf, hneg⟩
  · exact Or.inr ⟨tx, htx, a, ha, hrecv, hfresh, f, hf, hneg⟩

/-- **Each sign-split sample exhibits a SURK-CMA win against its key.** This is what
entitles the arm's named ε to be read as the adversary's SURK-CMA advantage: on every
sample of the `neg` half, the reduction's forgery converts (`toSURKWin`) into a win
against `−akP wV` or `akP wV` as `neg` directs, for any transcript whose messages lie
in `Signed`. -/
theorem spendAuthorityForgeryArm_win (S : SpendAuthShape P) (wV : KW) (hKB : kv.KB wV)
    {Signed : MSG → Prop} (hist : List (RedDSA.SigningAnswer F G MSG))
    (hhist : ∀ q ∈ hist, Signed q.m) {neg : Bool}
    {ω : ValidAnnotated P kv issuance maxActions}
    (hω : ω ∈ spendAuthorityForgeryArmEvent wV hKB Signed neg) :
    Nonempty (RedDSA.SURKWin S.sch (cond neg (-kv.akP wV) (kv.akP wV)) hist) := by
  obtain ⟨tx, htx, a, ha, hrecv, hfresh, f, _, hneg⟩ := hω
  exact ⟨hneg ▸ f.toSURKWin S hist hhist⟩

/-- **The forgery arm's ε, named honestly.** The forgery event's probability is at
most `εpos + εneg`, where the named hypotheses bound the two sign-split halves — by
`spendAuthorityForgeryArm_win`, the adversary's SURK-CMA advantage against `akP wV`
and against `−akP wV`. The sum is the design's factor-of-2. -/
theorem spendAuthorityForgery_measure_le
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (wV : KW) (hKB : kv.KB wV) (Signed : MSG → Prop) {εpos εneg : ℝ≥0∞}
    (hp : A.toOuterMeasure (spendAuthorityForgeryArmEvent wV hKB Signed false) ≤ εpos)
    (hn : A.toOuterMeasure (spendAuthorityForgeryArmEvent wV hKB Signed true) ≤ εneg) :
    A.toOuterMeasure (spendAuthorityForgeryEvent wV hKB Signed) ≤ εpos + εneg :=
  le_trans (toOuterMeasure_le_add₂ A (spendAuthorityForgeryEvent_subset wV hKB Signed))
    (add_le_add hp hn)

/-- **Spend Authority with the forgery arm at its SURK-CMA name.** The probability
that some Action spends a note addressed to `wV` over an unsigned sighash is at most
`εpos + εneg + εkb`: the SURK-CMA advantages at the two ± keys plus the key-binding arm's
ε — `spendAuthority_measure_le` with its forgery slot filled by
`spendAuthorityForgery_measure_le`. -/
theorem spendAuthority_measure_le_surk
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (wV : KW) (hKB : kv.KB wV) (Signed : MSG → Prop) {εpos εneg εkb : ℝ≥0∞}
    (hp : A.toOuterMeasure (spendAuthorityForgeryArmEvent wV hKB Signed false) ≤ εpos)
    (hn : A.toOuterMeasure (spendAuthorityForgeryArmEvent wV hKB Signed true) ≤ εneg)
    (hkb : A.toOuterMeasure (spendAuthorityBreakEvent wV hKB Signed) ≤ εkb) :
    A.toOuterMeasure (spendAuthorityViolation wV Signed) ≤ εpos + εneg + εkb :=
  spendAuthority_measure_le A wV hKB Signed
    (spendAuthorityForgery_measure_le A wV hKB Signed hp hn) hkb

end Arm

end Validity

end Zcash.Security.Ledger.Model
