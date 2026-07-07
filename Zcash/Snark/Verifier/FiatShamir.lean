import Mathlib
import Zcash.Snark.Core.ProofString
import Zcash.Snark.Core.Challenges
import Zcash.Snark.Verifier.Assemble

/-!
# Fiat-Shamir: the challenge schedule (hash hand-waved)

The deployed verifier is non-interactive: each challenge is a hash of the transcript absorbed so far,
rather than a fresh verifier coin. The hash is Blake2b (`transcript.rs`, personalization
`"Halo2-Transcript"`). Per project scope the hash is hand-waved *here*: this module models it as an abstract
`squeeze` function (`FiatShamir`) and does not formalize Blake2b. The random-oracle idealization of the
squeeze — reprogramming and the uniform-challenge bound the forking argument draws on — is separate, in
`Zcash.Snark.Soundness.Forking.Oracle`.

## What is pinned down

The schedule — which proof elements are absorbed before each challenge is squeezed — transcribed from
`plonk/verifier.rs`, `multiopen/verifier.rs`, and `commitment/verifier.rs`. This makes precise the
sense in which the deployed verifier is the Fiat-Shamir image of the interactive one
(`Zcash.Snark.Challenges` as genuine coins): the two differ only in the source of the challenges, and
`deriveChallenges` is that source. `nonInteractiveFingerprint` is then the deployed verifier's MSM,
`assemble` at the FS-derived challenges.

## Assumptions

* The Fiat-Shamir assumption (the random-oracle step) — that these hashed challenges carry the
  interactive verifier's soundness to the non-interactive setting. This is the explicit hand-wave. In
  the fingerprint match the challenges are taken from the captured real transcript, so the match never
  re-derives them and does not depend on this assumption.
-/

namespace Zcash.Snark

/-- An element written to the Fiat-Shamir transcript, carrying halo2's three Blake2b domain prefixes: a
commitment (group point, via `common_point` / `read_point`, `BLAKE2B_PREFIX_POINT`), a scalar (via
`common_scalar` / `read_scalar`, `BLAKE2B_PREFIX_SCALAR`), or the domain marker written before each
squeeze (`BLAKE2B_PREFIX_CHALLENGE`). The `challenge` marker — rather than re-absorbing the squeezed value —
is what makes consecutive squeezes differ, matching the deployed transcript (the prefix-byte writes persist
in the hash state; the challenge value is never fed back). -/
inductive TranscriptElt (F G : Type*) where
  | point : G → TranscriptElt F G
  | scalar : F → TranscriptElt F G
  | challenge : TranscriptElt F G

/-- The Fiat-Shamir hash, hand-waved: squeezes a field challenge from the transcript absorbed so far.
In the deployed verifier this is Blake2b; neither it nor the random-oracle reduction is modeled. -/
structure FiatShamir (F G : Type*) where
  squeeze : List (TranscriptElt F G) → F

/-- Absorb a vector of commitments. -/
def absorbPoints {F G : Type*} {a : ℕ} (f : Fin a → G) : List (TranscriptElt F G) :=
  List.ofFn (fun i => .point (f i))

/-- Absorb a vector of scalars. -/
def absorbScalars {F G : Type*} {a : ℕ} (f : Fin a → F) : List (TranscriptElt F G) :=
  List.ofFn (fun i => .scalar (f i))

/-- Absorb a per-sub-proof matrix of commitments. -/
def absorbPoints2 {F G : Type*} {a b : ℕ} (f : Fin a → Fin b → G) : List (TranscriptElt F G) :=
  (List.ofFn (fun i => absorbPoints (f i))).flatten

/-- Absorb a per-sub-proof matrix of scalars. -/
def absorbScalars2 {F G : Type*} {a b : ℕ} (f : Fin a → Fin b → F) : List (TranscriptElt F G) :=
  (List.ofFn (fun i => absorbScalars (f i))).flatten

/-- Absorb the lookup permuted commitments in the deployed order (halo2 `read_permuted_commitments`):
per proof, per lookup, the permuted-input commitment then the permuted-table commitment. -/
def absorbLookupPermuted {F G : Type*} {a b : ℕ} (input table : Fin a → Fin b → G) :
    List (TranscriptElt F G) :=
  (List.ofFn (fun p =>
    (List.ofFn (fun l => [TranscriptElt.point (input p l), TranscriptElt.point (table p l)])).flatten)).flatten

/-- Absorb a permutation set's evaluations (`eval`, `nextEval`, and `lastEval` when present). -/
def absorbPermSet {F G : Type*} (e : PermSetEval F) : List (TranscriptElt F G) :=
  [.scalar e.eval, .scalar e.nextEval] ++ (e.lastEval.map TranscriptElt.scalar).toList

/-- Absorb a lookup's five evaluations. -/
def absorbLookup {F G : Type*} (e : LookupEval F) : List (TranscriptElt F G) :=
  [.scalar e.productEval, .scalar e.productNextEval, .scalar e.permutedInputEval,
   .scalar e.permutedInputInvEval, .scalar e.permutedTableEval]

/-- Derive the verifier's challenges by Fiat-Shamir, following the deployed schedule
(`plonk/verifier.rs` → `multiopen/verifier.rs` → `commitment/verifier.rs`). Before each squeeze a
`TranscriptElt.challenge` domain marker (halo2's `BLAKE2B_PREFIX_CHALLENGE` byte) is appended, and the
squeezed challenge is *not* re-absorbed — matching the deployed Blake2b transcript, where the prefix-byte
writes persist in the hash state and the challenge value is never fed back. `init` is the pre-absorbed
prefix (the verifying-key hash and instance commitments). -/
def deriveChallenges {shape : Shape} {F G : Type*} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) : Challenges shape.k F :=
  -- advice commitments → θ
  let t := init ++ absorbPoints2 ps.adviceCommitments ++ [.challenge]
  let theta := fs.squeeze t
  -- lookup permuted commitments → β, γ
  let t := t ++ absorbLookupPermuted ps.lookupPermutedInput ps.lookupPermutedTable ++ [.challenge]
  let beta := fs.squeeze t
  let t := t ++ [.challenge]
  let gamma := fs.squeeze t
  -- permutation / lookup product commitments + vanishing random commitment → y
  let t := t ++ absorbPoints2 ps.permutationProduct ++ absorbPoints2 ps.lookupProduct
    ++ [TranscriptElt.point ps.vanishingRandom] ++ [.challenge]
  let y := fs.squeeze t
  -- quotient h pieces → x
  let t := t ++ absorbPoints ps.hPieces ++ [.challenge]
  let x := fs.squeeze t
  -- all evaluations → (multiopen) x₁, x₂
  let evalElts := absorbScalars2 ps.instanceEvals ++ absorbScalars2 ps.adviceEvals
    ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
    ++ absorbScalars ps.permutationCommonEvals
    ++ (List.ofFn (fun p => (List.ofFn (fun s => absorbPermSet (ps.permutationSetEvals p s))).flatten)).flatten
    ++ (List.ofFn (fun p => (List.ofFn (fun l => absorbLookup (ps.lookupEvals p l))).flatten)).flatten
  let t := t ++ evalElts ++ [.challenge]
  let x1 := fs.squeeze t
  let t := t ++ [.challenge]
  let x2 := fs.squeeze t
  -- q' → x₃
  let t := t ++ [TranscriptElt.point ps.multiopenQPrime] ++ [.challenge]
  let x3 := fs.squeeze t
  -- multiopen evals u → x₄
  let t := t ++ absorbScalars ps.multiopenU ++ [.challenge]
  let x4 := fs.squeeze t
  -- (IPA) S → ξ, z
  let t := t ++ [TranscriptElt.point ps.ipaS] ++ [.challenge]
  let xi := fs.squeeze t
  let t := t ++ [.challenge]
  let z := fs.squeeze t
  -- per IPA round: (Lⱼ, Rⱼ) → uⱼ
  let ipaRes := (List.finRange shape.k).foldl (fun (st : List (TranscriptElt F G) × List F) j =>
      let t := st.1 ++ [TranscriptElt.point (ps.ipaRounds j).1, TranscriptElt.point (ps.ipaRounds j).2,
        TranscriptElt.challenge]
      let uj := fs.squeeze t
      (t, st.2 ++ [uj])) (t, [])
  { theta := theta, beta := beta, gamma := gamma, y := y, x := x,
    x1 := x1, x2 := x2, x3 := x3, x4 := x4, xi := xi, z := z,
    ipaRound := fun j => ipaRes.2.getD j.val 0 }

/-- The deployed (non-interactive) verifier's fingerprint MSM: `assemble` at the Fiat-Shamir
challenges (the multiopen grouping is re-derived in Lean by `constructIntermediateSets`). The
Fiat-Shamir assumption (the random-oracle step) is what carries the interactive verifier's soundness to
this non-interactive MSM. -/
def nonInteractiveFingerprint {shape : Shape} {F G : Type*} [Field F] [DecidableEq F] [DecidableEq G]
    [Inhabited G] (fs : FiatShamir F G) (init : List (TranscriptElt F G))
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G) : Msm shape.k F G :=
  assemble vk ps (deriveChallenges fs init ps)

end Zcash.Snark
