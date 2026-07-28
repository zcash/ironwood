import Mathlib.Tactic

/-!
# RedDSA, abstractly

The RedDSA signature scheme (protocol spec §5.4.7,
<https://zips.z.cash/protocol/protocol.pdf#concretereddsa>), over an abstract
`(F, G)`-module in the style of `Zcash.Security.BindingSignature.Balance`. A scheme is a
base point `𝒫_G` with a challenge hash `H(R, vk, M)`; a signature is the
commitment/response pair `(R, S)`; verification is the Schnorr equation
`[S] 𝒫_G = R + [c] vk` at `c = H(R, vk, M)`. Key re-randomization (spec §4.1.7.1,
<https://zips.z.cash/protocol/protocol.pdf#abstractsigrerand>) is `sk + α` on private
keys and `vk + [α] 𝒫_G` on public keys.

## Abstraction boundary

Byte encodings are elided — the challenge hash consumes group elements directly — and
Validate's cofactor multiplication `[h_G]` is dropped: the deployed instantiations of
interest here are on Pallas (`SpendAuthSig^Orchard` with the spend-auth base,
`BindingSig^Orchard` with the value-commitment randomness base ℛ), and Pallas is
prime-order, `h_ℙ = 1`. The spec's canonical-encoding check on `R` (the ZIP 216 rule)
has no abstract counterpart: group elements have no encoding to be non-canonical in.
The concrete instantiation must carry both; see the caveat in
`Zcash.Security.RedDSA.SURK`.

## What this module proves, and what stays named

* The spec's re-randomization axioms, at this instantiation: re-randomization commutes
  with key derivation (`derivePublic_randomizePrivate`), is invertible
  (`randomizePrivate_add_neg`), and key derivation is an injective homomorphism
  (`derivePublic_add`, `derivePublic_injective` — the §4.1.7.2 key monomorphism the
  binding-signature sum `bvk = [Σ rcv] ℛ` rests on).
* Completeness (`verify_sign`, `verify_sign_randomized`) — the formalized verification
  equation is the one honest signers satisfy, under original and re-randomized keys.
* Special soundness (`forkDlog_spec`, `verify_fork_dlog`) — two verifying transcripts
  sharing a commitment under distinct challenges compute `dlog vk`, as data. This is
  the deterministic core a Fiat–Shamir fork hands the knowledge extractor; the
  rewinding's probability accounting (the knowledge error) is *not* proven here — it
  stays a named `κ`, consumed by the transaction-balance premiss discharge
  (`Zcash.Security.Ledger.ValueExtraction`).
* `ExtractionFailure` — the event that `κ` bounds, as data: a verifying signature on
  which a candidate extractor does not return the key's discrete log. The spec's
  demand on `BindingSig` is exactly a knowledge property ("a signature must prove
  knowledge of the discrete logarithm of the validating key with respect to the base
  ℛ", §5.4.7.2); carrying the failure as data keeps its probability a bound on an
  exhibited event, not a total extraction hypothesis (which is classically satisfiable
  in a cyclic group — see the module doc of `Zcash.Security.Ledger.Value`).
-/

namespace Zcash.Security.RedDSA

variable {F G MSG : Type*}

/-- An abstract RedDSA scheme: the base point `𝒫_G` of the instantiation (spec §5.4.7
leaves it a parameter — the spend-auth base for `SpendAuthSig`, the value-commitment
randomness base ℛ for `BindingSig`) and the challenge hash `H(R, vk, M)`, the
byte-level `H^⊛(R̄ ∥ v̄k ∥ M)` with encodings elided. That `vk` is hashed is
load-bearing for unforgeability across re-randomized keys — see
`verify_shifted_of_key_blind_hash`. -/
structure Scheme (F G MSG : Type*) where
  /-- The generator `𝒫_G` of the instantiation. -/
  base : G
  /-- The challenge hash `H(R, vk, M)`, abstracting `H^⊛(R̄ ∥ v̄k ∥ M)`. -/
  H : G → G → MSG → F

/-- A RedDSA signature, decoded: the commitment `R = [r] 𝒫_G` and the response
`S = r + c · sk`. The byte-level signature is the 64-byte `R̄ ∥ S̄`. -/
structure Sig (F G : Type*) where
  R : G
  S : F

section Module

variable [Field F] [AddCommGroup G] [Module F G]

/-- Key derivation: `vk = [sk] 𝒫_G`. -/
def Scheme.derivePublic (sch : Scheme F G MSG) (sk : F) : G := sk • sch.base

/-- Signing with nonce `r`: `R = [r] 𝒫_G`, `S = r + H(R, vk, M) · sk`. The spec derives
the nonce by hashing 80 uniform bytes (`H^⊛(T ∥ v̄k ∥ M)`); here it is a parameter —
its distribution is the probability layer's concern, and none of the algebra below
depends on it. -/
def Scheme.sign (sch : Scheme F G MSG) (sk r : F) (m : MSG) : Sig F G :=
  ⟨r • sch.base, r + sch.H (r • sch.base) (sch.derivePublic sk) m * sk⟩

/-- The verification equation: `[S] 𝒫_G = R + [c] vk` at `c = H(R, vk, M)` — spec
§5.4.7's Validate, with encodings elided and the cofactor multiplication dropped
(`h_ℙ = 1`; see the module doc's abstraction boundary). -/
def Scheme.Verify (sch : Scheme F G MSG) (vk : G) (m : MSG) (σ : Sig F G) : Prop :=
  σ.S • sch.base = σ.R + sch.H σ.R vk m • vk

/-- Private-key re-randomization: `sk + α` (spec §4.1.7.1). -/
def randomizePrivate (α sk : F) : F := sk + α

/-- Public-key re-randomization: `vk + [α] 𝒫_G` (spec §4.1.7.1). The shape the ledger
model's `Primitives.randomizePublic` is pinned to by `SpendAuthShape`. -/
def Scheme.randomizePublic (sch : Scheme F G MSG) (α : F) (vk : G) : G :=
  vk + α • sch.base

/-- Re-randomization is invertible: randomizing by `−α` undoes randomizing by `α`
(spec §4.1.7.1's "injective and easily invertible", and its knowledge-transfer note —
whoever knows `sk + α` and `α` knows `sk`). -/
theorem randomizePrivate_add_neg (α sk : F) :
    randomizePrivate (-α) (randomizePrivate α sk) = sk := by
  simp [randomizePrivate]

/-- Re-randomization commutes with key derivation: the public randomization of the
derived key is the derived key of the private randomization (spec §4.1.7.1, the axiom
relating the two randomizers). This is what makes the single-oracle SURK-CMA
experiment well-posed: the oracle signs under `sk + α`, and the adversary can compute
the matching verification key `vk + [α] 𝒫_G`. -/
theorem Scheme.derivePublic_randomizePrivate (sch : Scheme F G MSG) (α sk : F) :
    sch.derivePublic (randomizePrivate α sk) = sch.randomizePublic α (sch.derivePublic sk) := by
  simp only [derivePublic, randomizePrivate, randomizePublic, add_smul, add_comm]

/-- Key derivation is additive — the §4.1.7.2 key monomorphism. This is the property
the binding-signature construction rests on: `bvk = Σ cv − ValueCommit_0(vBalance)`
equals `[Σ rcv] ℛ`, the derived key of the randomness sum. -/
theorem Scheme.derivePublic_add (sch : Scheme F G MSG) (sk₁ sk₂ : F) :
    sch.derivePublic (sk₁ + sk₂) = sch.derivePublic sk₁ + sch.derivePublic sk₂ := by
  simp only [derivePublic, add_smul]

/-- Key derivation from a nonzero base is injective (spec §4.1.7 requires it of
`DerivePublic`; concretely `𝒫_G` has full order `r_G`). -/
theorem Scheme.derivePublic_injective (sch : Scheme F G MSG) [NoZeroSMulDivisors F G]
    (hbase : sch.base ≠ 0) : Function.Injective sch.derivePublic := by
  intro sk₁ sk₂ h
  simp only [derivePublic] at h
  have hz : (sk₁ - sk₂) • sch.base = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp hz with hc | hb
  · exact sub_eq_zero.mp hc
  · exact absurd hb hbase

/-- Deriving from the negated key negates the derived key: `[−sk] 𝒫_G = −[sk] 𝒫_G`.
The algebra behind the `±` extension of the unforgeability hypothesis: a forgery
against `−vk` is a forgery against the verification key of `−sk`, so the ±-extended
hypothesis is the plain one at two related keys (see `Zcash.Security.RedDSA.SURK`). -/
theorem Scheme.derivePublic_neg (sch : Scheme F G MSG) (sk : F) :
    sch.derivePublic (-sk) = -sch.derivePublic sk := by
  simp only [derivePublic, neg_smul]

/-- Completeness: an honestly-signed signature verifies. -/
theorem Scheme.verify_sign (sch : Scheme F G MSG) (sk r : F) (m : MSG) :
    sch.Verify (sch.derivePublic sk) m (sch.sign sk r m) := by
  simp only [Verify, sign, derivePublic, add_smul, mul_smul]

/-- Completeness under re-randomized keys: signing under `sk + α` verifies under
`vk + [α] 𝒫_G` — the SURK-CMA oracle's honest answers verify. -/
theorem Scheme.verify_sign_randomized (sch : Scheme F G MSG) (sk α r : F) (m : MSG) :
    sch.Verify (sch.randomizePublic α (sch.derivePublic sk)) m
      (sch.sign (randomizePrivate α sk) r m) := by
  rw [← sch.derivePublic_randomizePrivate]
  exact sch.verify_sign _ r m

/-! ### Special soundness: the forking extractor's deterministic core

A rewinding argument runs the signer twice, reprogramming the random oracle at the
challenge query `(R, vk, M)` between runs. On a double success it holds two verifying
transcripts sharing the commitment `R` under distinct challenges, and the subtraction
below computes `dlog_{𝒫_G} vk`. That is the extractor's whole deterministic content;
what forking adds is the probability that the double success occurs — the knowledge
error, a named quantity here. -/

/-- The scalar a fork computes: `(c₁ − c₂)⁻¹ · (S₁ − S₂)`. -/
def forkDlog (S₁ S₂ c₁ c₂ : F) : F := (c₁ - c₂)⁻¹ * (S₁ - S₂)

/-- **Special soundness, on the raw equations.** Two verification equations sharing
`base`, `vk`, and the commitment `R`, under distinct challenges, force
`vk = [forkDlog] base`. -/
theorem forkDlog_spec {base vk R : G} {S₁ S₂ c₁ c₂ : F} (hc : c₁ ≠ c₂)
    (h₁ : S₁ • base = R + c₁ • vk) (h₂ : S₂ • base = R + c₂ • vk) :
    vk = forkDlog S₁ S₂ c₁ c₂ • base := by
  have hsub : (S₁ - S₂) • base = (c₁ - c₂) • vk := by
    rw [sub_smul, h₁, h₂, sub_smul]
    abel
  have hcne : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hc
  calc vk = ((c₁ - c₂)⁻¹ * (c₁ - c₂)) • vk := by
        rw [inv_mul_cancel₀ hcne, one_smul]
    _ = (c₁ - c₂)⁻¹ • ((c₁ - c₂) • vk) := by rw [mul_smul]
    _ = (c₁ - c₂)⁻¹ • ((S₁ - S₂) • base) := by rw [hsub]
    _ = forkDlog S₁ S₂ c₁ c₂ • base := by rw [smul_smul, forkDlog]

/-- **Special soundness, at the scheme level.** Two verifier runs under reprogrammed
challenge hashes `H₁`, `H₂` over the same base, accepting signatures that share the
commitment `R` on the same `(vk, m)`, with the hashes disagreeing at the challenge
query, compute the discrete log of `vk` — the shape a Fiat–Shamir fork hands the
extractor. -/
theorem verify_fork_dlog {base : G} {H₁ H₂ : G → G → MSG → F} {vk R : G} {m : MSG}
    {S₁ S₂ : F}
    (hv₁ : Scheme.Verify ⟨base, H₁⟩ vk m ⟨R, S₁⟩)
    (hv₂ : Scheme.Verify ⟨base, H₂⟩ vk m ⟨R, S₂⟩)
    (hc : H₁ R vk m ≠ H₂ R vk m) :
    vk = forkDlog S₁ S₂ (H₁ R vk m) (H₂ R vk m) • base :=
  forkDlog_spec hc hv₁ hv₂

/-! ### Extraction failure, as data -/

/-- A candidate knowledge extractor: from a verifying `(vk, m, σ)` it should return
`dlog_{𝒫_G} vk`. Total as a function; where it fails is exactly the event the
knowledge error bounds. -/
abbrev Extractor (F G MSG : Type*) := G → MSG → Sig F G → F

/-- An extraction failure, as data: a verifying signature on which the extractor does
not return the discrete log of `vk`. The knowledge obligation on `BindingSig` — "a
signature must prove knowledge of the discrete logarithm of the validating key with
respect to the base ℛ" (spec §5.4.7.2) — is the named bound `κ` on the probability
that an adversary exhibits this event; its eventual discharge is the random-oracle
forking argument whose deterministic core is `verify_fork_dlog`. -/
structure ExtractionFailure (sch : Scheme F G MSG) (E : Extractor F G MSG) where
  vk : G
  m : MSG
  σ : Sig F G
  verifies : sch.Verify vk m σ
  ne : vk ≠ E vk m σ • sch.base

end Module

end Zcash.Security.RedDSA
