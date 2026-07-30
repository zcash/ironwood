import Mathlib.Tactic
import Zcash.Security.RedDSA.Basic

/-!
# SURK-CMA: strong unforgeability with re-randomized keys

The unforgeability notion the spec requires of every `SpendAuthSig` instantiation
(spec §4.1.7.1, <https://zips.z.cash/protocol/protocol.pdf#abstractsigrerand>, after
[FKMSSS2016, section 3]): **S**trong **U**nforgeability with **R**e-randomized
**K**eys under adaptive **C**hosen **M**essage **A**ttack. The adversary holds
`vk = DerivePublic(sk)` and a single signing oracle `O_sk`; a query `(m, α)` is
answered by `Sign_{sk + α}(m)`, and the oracle records the pair `(m, σ)` in its state
`Q`. The adversary wins by outputting `(m′, σ′, α′)` with
`Validate_{RandomizePublic(α′, vk)}(m′, σ′) = 1` and `(m′, σ′) ∉ Q`. *Strong* is the
pair-level freshness: a new signature on a previously-signed message is a win.

## What is formalized

Following the repo's split — deterministic exhibitions now, probability accounting at
the named layer — this module formalizes the *win*: the object whose probability the
named SURK-CMA hypothesis bounds, judged against a transcript of answered oracle
queries. The interaction that produces the transcript (adaptive queries, nonce and key
sampling) is not modelled; a win is judged against an arbitrary transcript, which only
widens the event. `SURKWin` carries the winning triple as data;
`SURKWin.ofMessageFresh` is the a-fortiori step the Spend Authority forgery arm uses,
whose freshness (`SpendAuthForgery.fresh`) is message-level — strictly stronger than
the pair-level clause it must discharge.

## Checking the game definition

The experiment is the spec author's own formulation, so the definition itself is
audited here, not only consumed:

* **Single oracle vs. the literature's two.** [FKMSSS2016] gives the adversary two
  oracles — plain-key signing and randomized-key signing — because its syntax has no
  identity randomizer. The spec adds one (`𝒪 = 0` with `RandomizePrivate_𝒪 = id`) and
  merges the oracles: a query at `α = 0` *is* the plain-key oracle
  (`randomizePrivate_zero`, `randomizePublic_zero`), so each game simulates the other
  query-for-query with no advantage loss. The simplification is an interface
  repackaging, not a weakening. The spec's game also differs from [FKMSSS2016,
  Definition 8] in being *strong* (pair freshness, not message freshness) — a strictly
  stronger demand on the scheme, which the spec flags itself.
* **The two sides talk about the same keys.** The oracle signs under `sk + α` while
  the win is judged under `RandomizePublic(α′, vk)`;
  `Scheme.derivePublic_randomizePrivate` proves these agree and
  `Scheme.verify_sign_randomized` proves the oracle's honest answers verify, so the
  game is well-posed and non-vacuous.
* **Freshness ignores randomizers, so the key must be hashed.** `Q` records `(m, σ)`
  without the query's `α`, so a signature *transported* to a different randomization
  of `vk` would count as a win. For a Schnorr scheme whose challenge hash ignores the
  verification key, that transport exists — `verify_shifted_of_key_blind_hash` maps a
  verifying `(R, S)` under `vk` to a verifying `(R, S + c·α′)` under any
  `RandomizePublic(α′, vk)` — and SURK-CMA breaks trivially. RedDSA hashes
  `v̄k` into the challenge (`H^⊛(R̄ ∥ v̄k ∥ M)`) precisely to cut this off: the
  key-prefixing is load-bearing, not an EdDSA-inherited accident. It also carries the
  multi-user tightness line: the claimed tight multi-user→single-user reduction for
  plain Schnorr (Galbraith–Malone-Lee–Smart) was flawed, Bernstein showed the
  key-prefixed scheme admits it (eprint 2015/996), and Kiltz–Masny–Pan treat it
  systematically (eprint 2016/191); SURK-CMA's re-randomized keys are effectively a
  multi-key setting.
* **Two idealizations at the abstract layer, flagged.** (1) Signatures here are
  group/scalar pairs, so "same signature" is unambiguous; the deployed byte-level
  scheme accepts encodings whose canonicity ZIP 216 had to legislate, and pair
  freshness over *encodings* is weaker than over abstract pairs unless the concrete
  instantiation carries that canonicalization. (2) The spec's re-randomization axioms
  ask that `sk + α` at random `α` be *identically* distributed to a fresh key;
  RedDSA's `GenRandom` (a hash into `𝔽_{r_G}`) achieves this only up to statistical
  distance ≈ 2⁻¹²⁸. Both belong to the concrete instantiation; neither affects the
  algebra below.

## The ± extension

Spend Authority consumes the hypothesis at *two* keys, the victim's `akV` and its
negation (`SpendAuthForgery.negated`): the circuit pins `ak^ℙ` only up to the sign of
its y-coordinate, which the spec accepts as knowledge of `ask` up to sign (§4.18.4
note). `SURKWin.negKey` gives the honest reading: a win against `−vk` is a win against
the verification key of `−sk` (`derivePublic_neg`), so the ±-extended hypothesis is
the plain SURK-CMA assumption at two related keys — the design's accepted factor-of-2
loss, not a new notion.
-/

namespace Zcash.Security.RedDSA

variable {F G MSG : Type*}

/-- One answered query of the SURK-CMA signing oracle: the adversary chose `(m, α)`,
the oracle answered `σ = Sign_{sk + α}(m)`. The oracle's state `Q` records only the
pair `(m, σ)`; the freshness clause of `SURKWin` accordingly ignores `α`. -/
structure SigningAnswer (F G MSG : Type*) where
  m : MSG
  α : F
  σ : Sig F G

section Module

variable [Field F] [AddCommGroup G] [Module F G]

/-- Re-randomization by the identity randomizer `𝒪 = 0` is the identity on private
keys: the spec's single signing oracle at `α = 0` is the literature's plain-key
oracle. -/
theorem randomizePrivate_zero (sk : F) : randomizePrivate 0 sk = sk := add_zero sk

/-- Re-randomization by `𝒪 = 0` is the identity on public keys: a win at `α′ = 0` is
a forgery under the original `vk`. -/
theorem Scheme.randomizePublic_zero (sch : Scheme F G MSG) (vk : G) :
    sch.randomizePublic 0 vk = vk := by
  simp [randomizePublic]

/-- **A key-blind challenge hash forfeits SURK-CMA.** If `H` ignores its key argument,
any verifying `(R, S)` under `vk` transports to a verifying `(R, S + c·α)` under any
re-randomization of `vk` — with the message unchanged and the transcript recording
only `(m, σ)` pairs, a fresh win at every `α` with `c · α ≠ 0`. RedDSA hashes the
verification key into the challenge to cut this transport off. -/
theorem Scheme.verify_shifted_of_key_blind_hash (sch : Scheme F G MSG)
    (hH : ∀ R k k' m, sch.H R k m = sch.H R k' m)
    {vk R : G} {S : F} {m : MSG} (hv : sch.Verify vk m ⟨R, S⟩) (α : F) :
    sch.Verify (sch.randomizePublic α vk) m ⟨R, S + sch.H R vk m * α⟩ := by
  simp only [Verify] at hv ⊢
  rw [hH R (sch.randomizePublic α vk) vk m, Scheme.randomizePublic, smul_add, add_smul,
    hv, mul_smul]
  abel

/-- **A SURK-CMA win against `vk`, as data**, judged against the transcript `hist`: a
triple `(m′, σ′, α′)` whose signature verifies under the re-randomization of `vk` by
`α′`, with the pair `(m′, σ′)` differing from every answered `(mᵢ, σᵢ)` — strong
freshness, randomizers ignored. The named SURK-CMA hypothesis bounds the probability
that an adversary exhibits this object; this layer never bounds it. -/
structure SURKWin (sch : Scheme F G MSG) (vk : G) (hist : List (SigningAnswer F G MSG)) where
  m : MSG
  σ : Sig F G
  α : F
  verifies : sch.Verify (sch.randomizePublic α vk) m σ
  fresh : ∀ q ∈ hist, ¬ (q.m = m ∧ q.σ = σ)

/-- The a-fortiori step: a verifying signature under a re-randomization of `vk` whose
*message* was never signed is a SURK-CMA win — message freshness implies pair
freshness. This is the builder the Spend Authority forgery arm uses. -/
def SURKWin.ofMessageFresh {sch : Scheme F G MSG} {vk : G}
    {hist : List (SigningAnswer F G MSG)} {Signed : MSG → Prop} (m : MSG) (σ : Sig F G)
    (α : F) (verifies : sch.Verify (sch.randomizePublic α vk) m σ)
    (hhist : ∀ q ∈ hist, Signed q.m) (hfresh : ¬ Signed m) :
    SURKWin sch vk hist :=
  ⟨m, σ, α, verifies, fun q hq ⟨hm, _⟩ => hfresh (hm ▸ hhist q hq)⟩

/-- A win against the verification key of `−sk` is a win against the negated
verification key: the ± extension of the unforgeability hypothesis is the plain
hypothesis at the two keys `± sk`. -/
def SURKWin.negKey {sch : Scheme F G MSG} {sk : F} {hist : List (SigningAnswer F G MSG)}
    (w : SURKWin sch (sch.derivePublic (-sk)) hist) :
    SURKWin sch (-sch.derivePublic sk) hist :=
  sch.derivePublic_neg sk ▸ w

end Module

end Zcash.Security.RedDSA
