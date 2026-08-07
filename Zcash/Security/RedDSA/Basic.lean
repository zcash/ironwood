import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# RedDSA, abstractly

The RedDSA signature scheme (protocol spec §5.4.7,
<https://zips.z.cash/protocol/protocol.pdf#concretereddsa>), over an abstract
`(F, G)`-module in the style of `Zcash.Security.BindingSignature.Balance`. A scheme
is a base point 𝒫_𝔾 with a challenge hash H(R, vk, M); a signature is the
commitment/response pair (R, S); verification is the Schnorr equation
[S] 𝒫_𝔾 = R + [c] vk at c = H(R, vk, M). Key re-randomization (spec §4.1.7.1,
<https://zips.z.cash/protocol/protocol.pdf#abstractsigrerand>) is sk + α on private
keys and vk + [α] 𝒫_𝔾 on public keys.

## Abstraction boundary

Byte encodings are elided — the challenge hash consumes group elements directly — and
Validate's cofactor multiplication [h_𝔾] is dropped: the deployed instantiations of
interest here are on Pallas (SpendAuthSig^Orchard with the spend-auth base 𝒢^Orchard,
BindingSig^Orchard with the value-commitment randomness base ℛ^Orchard), and Pallas
is prime-order, h_ℙ = 1. The spec's canonical-encoding check on R (the ZIP 216 rule)
has no abstract counterpart: group elements have no encoding to be non-canonical in.
The concrete instantiation must carry both.

## What this module proves, and what stays named

* The spec's re-randomization axioms, at this instantiation: re-randomization commutes
  with key derivation (`derivePublic_randomizePrivate`), is invertible
  (`randomizePrivate_add_neg`), and key derivation is an injective homomorphism
  (`derivePublic_add`, `derivePublic_injective` — the §4.1.7.2 key monomorphism the
  binding-signature sum bvk = [Σ rcv] ℛ rests on).
* Completeness (`verify_sign`, `verify_sign_randomized`) — the formalized verification
  equation is the one honest signers satisfy, under original and re-randomized keys.
The extraction notions — a candidate extractor and its failures as data, the event that κ
bounds — live in `Zcash.Security.RedDSA.Extraction` beside the deterministic extraction core.

## Discharge routes (none chosen here)

Two routes to discharging the named bounds are known for Schnorr-like schemes. The
classical one is the random-oracle forking argument (rewind the signer, reprogram
the challenge at the fork point), whose deterministic core is special soundness:
two verifying transcripts sharing a commitment under distinct challenges yield the
discrete log. Its probability accounting carries a multiplicative loss that is
essentially optimal for ROM-only reductions from discrete log (Seurin, eprint
2012/029). In the AGM+ROM —the model the Halo 2 knowledge-soundness layer already
rests on— Fuchsbauer, Plouviez, and Seurin give a tight, straight-line reduction to
discrete log (eprint 2019/877, section 3, Theorem 1), with no rewinding and only
additive statistical loss. Their theorem covers plain non-key-prefixed Schnorr under
EUF-CMA, so its adaptation to RedDSA —the key-prefixed hash, strong notion of
freshness, and re-randomized keys— is unchecked.
-/

namespace Zcash.Security.RedDSA

variable {F G MSG : Type*}

/-- An abstract RedDSA scheme (spec §5.4.7), with its parameters:
* the base point 𝒫_𝔾 of the instantiation — the spend-auth base 𝒢^Orchard
  (§5.4.7.1) or the value-commitment randomness base ℛ^Orchard (§5.4.7.2);
* the challenge hash H(R, vk, M), abstracting the byte-level
  H^⊛(R_bytes || vk_bytes || M) with encodings elided.

That an encoding of vk is hashed is load-bearing for unforgeability across
re-randomized keys: a key-blind challenge hash would let a verifying signature
transport across re-randomizations of vk, and the key-prefixing also carries the
multi-user tightness line (Bernstein, eprint 2015/996; Kiltz–Masny–Pan, eprint
2016/191). -/
structure Scheme (F G MSG : Type*) where
  /-- The generator 𝒫_𝔾 of the instantiation. -/
  base : G
  /-- The challenge hash H(R, vk, M), abstracting H^⊛(R_bytes || vk_bytes || M). -/
  H : G → G → MSG → F

/-- A RedDSA signature, decoded: the commitment R = [r] 𝒫_𝔾 and the response
S = r + c · sk. The byte-level signature is the 64-byte R_bytes || S_bytes. -/
structure Sig (F G : Type*) where
  R : G
  S : F

section Module

variable [Field F] [AddCommGroup G] [Module F G]

/-- Key derivation: vk = [sk] 𝒫_𝔾. -/
def Scheme.derivePublic (sch : Scheme F G MSG) (sk : F) : G := sk • sch.base

/-- Signing with randomness r: R = [r] 𝒫_𝔾, S = r + H(R, vk, M) · sk. The spec
derives r by hashing 80 uniform bytes (H^⊛(T || vk_bytes || M)). Here it is a
parameter; its distribution is the probability layer's concern, and none of the
algebra below depends on it. -/
def Scheme.sign (sch : Scheme F G MSG) (sk r : F) (m : MSG) : Sig F G :=
  ⟨r • sch.base, r + sch.H (r • sch.base) (sch.derivePublic sk) m * sk⟩

/-- The verification equation: [S] 𝒫_𝔾 = R + [c] vk at c = H(R, vk, M). This is
spec §5.4.7's Validate, with encodings elided and the cofactor multiplication dropped,
since for Pallas h_ℙ = 1. -/
def Scheme.Verify (sch : Scheme F G MSG) (vk : G) (m : MSG) (σ : Sig F G) : Prop :=
  σ.S • sch.base = σ.R + sch.H σ.R vk m • vk

/-- Private-key re-randomization: sk + α (spec §4.1.7.1). -/
def randomizePrivate (α sk : F) : F := sk + α

/-- Public-key re-randomization: vk + [α] 𝒫_𝔾 (spec §4.1.7.1). -/
def Scheme.randomizePublic (sch : Scheme F G MSG) (α : F) (vk : G) : G :=
  vk + α • sch.base

/-- Re-randomization is invertible: randomizing by −α undoes randomizing by α
(spec §4.1.7.1's "injective and easily invertible", and its knowledge-transfer note —
whoever knows sk + α and α knows sk). -/
theorem randomizePrivate_add_neg (α sk : F) :
    randomizePrivate (-α) (randomizePrivate α sk) = sk := by
  simp [randomizePrivate]

/-- Re-randomization commutes with key derivation: the public randomization of the
derived key is the derived key of the private randomization (spec §4.1.7.1, the axiom
relating the two randomizers). This is what makes the spec's single-oracle SURK-CMA
experiment well-posed: the oracle signs under sk + α, and the adversary can compute
the matching verification key vk + [α] 𝒫_𝔾. -/
theorem Scheme.derivePublic_randomizePrivate (sch : Scheme F G MSG) (α sk : F) :
    sch.derivePublic (randomizePrivate α sk) = sch.randomizePublic α (sch.derivePublic sk) := by
  simp only [derivePublic, randomizePrivate, randomizePublic, add_smul, add_comm]

/-- Key derivation is additive — the §4.1.7.2 key monomorphism. This is the property
the binding-signature construction rests on: bvk = Σ cv − ValueCommit_0(vBalance)
equals [Σ rcv] ℛ, the derived key of the randomness sum. -/
theorem Scheme.derivePublic_add (sch : Scheme F G MSG) (sk₁ sk₂ : F) :
    sch.derivePublic (sk₁ + sk₂) = sch.derivePublic sk₁ + sch.derivePublic sk₂ := by
  simp only [derivePublic, add_smul]

/-- Key derivation from a nonzero base is injective (spec §4.1.7 requires it of
DerivePublic; concretely 𝒫_𝔾 has full order r_𝔾). -/
theorem Scheme.derivePublic_injective (sch : Scheme F G MSG) [NoZeroSMulDivisors F G]
    (hbase : sch.base ≠ 0) : Function.Injective sch.derivePublic := by
  intro sk₁ sk₂ h
  simp only [derivePublic] at h
  have hz : (sk₁ - sk₂) • sch.base = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp hz with hc | hb
  · exact sub_eq_zero.mp hc
  · exact absurd hb hbase

/-- Completeness: an honestly-signed signature verifies. -/
theorem Scheme.verify_sign (sch : Scheme F G MSG) (sk r : F) (m : MSG) :
    sch.Verify (sch.derivePublic sk) m (sch.sign sk r m) := by
  simp only [Verify, sign, derivePublic, add_smul, mul_smul]

/-- Completeness under re-randomized keys: signing under sk + α verifies under
vk + [α] 𝒫_𝔾 — the spec's SURK-CMA oracle's honest answers verify. -/
theorem Scheme.verify_sign_randomized (sch : Scheme F G MSG) (sk α r : F) (m : MSG) :
    sch.Verify (sch.randomizePublic α (sch.derivePublic sk)) m
      (sch.sign (randomizePrivate α sk) r m) := by
  rw [← sch.derivePublic_randomizePrivate]
  exact sch.verify_sign _ r m

/-- Re-randomization by the identity randomizer 𝒪 = `0` is the identity on private
keys. -/
theorem randomizePrivate_zero (sk : F) : randomizePrivate 0 sk = sk := add_zero sk

/-- Re-randomization by 𝒪 = `0` is the identity on public keys. -/
theorem Scheme.randomizePublic_zero (sch : Scheme F G MSG) (vk : G) :
    sch.randomizePublic 0 vk = vk := by
  simp [randomizePublic]

end Module

end Zcash.Security.RedDSA
