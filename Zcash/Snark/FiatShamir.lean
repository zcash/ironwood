import Mathlib
import Zcash.Snark.ProofString
import Zcash.Snark.Challenges
import Zcash.Snark.Assemble

/-!
# Fiat-Shamir (hand-waved)

The deployed verifier is non-interactive: each challenge is a hash of the transcript absorbed so far,
rather than a fresh verifier coin. In the deployed code that hash is **Blake2b** (`transcript.rs`,
personalization `"Halo2-Transcript"`) — not BLAKE3 (BLAKE3 is Ironwood's txid hash, not the SNARK
transcript). Per project scope, Fiat-Shamir is **hand-waved**: we model the hash as an abstract
`squeeze` function (`FiatShamir`) and do not formalize Blake2b or the random-oracle reduction.

What this module *does* pin down is the **schedule** — which proof elements are absorbed before each
challenge is squeezed — transcribed from `plonk/verifier.rs`, `multiopen/verifier.rs`, and
`commitment/verifier.rs`. This makes precise the sense in which the deployed verifier is the
Fiat-Shamir image of the interactive one (`Zcash.Snark.Challenges` as genuine coins): the two differ
only in the *source* of the challenges, and `deriveChallenges` is that source.

`nonInteractiveFingerprint` is then the deployed verifier's MSM: `assembleFinalMsm` at the FS-derived
challenges. **The Fiat-Shamir assumption** — that these hashed challenges carry the interactive
verifier's soundness to the non-interactive setting (the random-oracle step) — is the explicit
hand-wave; in the fingerprint match the challenges are taken from the captured real transcript, so the
match never re-derives them and does not depend on this assumption.
-/

namespace Zcash.Snark

/-- An element absorbed into the Fiat-Shamir transcript: a commitment (group point, via `common_point`
/ `read_point`) or a scalar (via `common_scalar` / `read_scalar`). -/
inductive TranscriptElt (F G : Type*) where
  | point : G → TranscriptElt F G
  | scalar : F → TranscriptElt F G

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

/-- Absorb a permutation set's evaluations (`eval`, `nextEval`, and `lastEval` when present). -/
def absorbPermSet {F G : Type*} (e : PermSetEval F) : List (TranscriptElt F G) :=
  [.scalar e.eval, .scalar e.nextEval] ++ (e.lastEval.map TranscriptElt.scalar).toList

/-- Absorb a lookup's five evaluations. -/
def absorbLookup {F G : Type*} (e : LookupEval F) : List (TranscriptElt F G) :=
  [.scalar e.productEval, .scalar e.productNextEval, .scalar e.permutedInputEval,
   .scalar e.permutedInputInvEval, .scalar e.permutedTableEval]

/-- Derive the verifier's challenges by Fiat-Shamir, following the deployed schedule
(`plonk/verifier.rs` → `multiopen/verifier.rs` → `commitment/verifier.rs`). After each squeeze the
challenge is appended to the transcript (the deployed transcript reseeds with it), so consecutive
squeezes differ. `init` is the pre-absorbed prefix (the verifying-key hash and instance commitments). -/
def deriveChallenges {shape : Shape} {F G : Type*} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) : Challenges shape.k F :=
  -- advice commitments → θ
  let t := init ++ absorbPoints2 ps.adviceCommitments
  let theta := fs.squeeze t
  -- lookup permuted commitments → β, γ
  let t := t ++ [.scalar theta] ++ absorbPoints2 ps.lookupPermutedInput ++ absorbPoints2 ps.lookupPermutedTable
  let beta := fs.squeeze t
  let t := t ++ [.scalar beta]
  let gamma := fs.squeeze t
  -- permutation / lookup product commitments + vanishing random commitment → y
  let t := t ++ [.scalar gamma] ++ absorbPoints2 ps.permutationProduct ++ absorbPoints2 ps.lookupProduct
    ++ [TranscriptElt.point ps.vanishingRandom]
  let y := fs.squeeze t
  -- quotient h pieces → x
  let t := t ++ [.scalar y] ++ absorbPoints ps.hPieces
  let x := fs.squeeze t
  -- all evaluations → (multiopen) x₁, x₂
  let evalElts := absorbScalars2 ps.instanceEvals ++ absorbScalars2 ps.adviceEvals
    ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
    ++ absorbScalars ps.permutationCommonEvals
    ++ (List.ofFn (fun p => (List.ofFn (fun s => absorbPermSet (ps.permutationSetEvals p s))).flatten)).flatten
    ++ (List.ofFn (fun p => (List.ofFn (fun l => absorbLookup (ps.lookupEvals p l))).flatten)).flatten
  let t := t ++ [.scalar x] ++ evalElts
  let x1 := fs.squeeze t
  let t := t ++ [.scalar x1]
  let x2 := fs.squeeze t
  -- q' → x₃
  let t := t ++ [.scalar x2] ++ [TranscriptElt.point ps.multiopenQPrime]
  let x3 := fs.squeeze t
  -- multiopen evals u → x₄
  let t := t ++ [.scalar x3] ++ absorbScalars ps.multiopenU
  let x4 := fs.squeeze t
  -- (IPA) S → ξ, z
  let t := t ++ [.scalar x4] ++ [TranscriptElt.point ps.ipaS]
  let xi := fs.squeeze t
  let t := t ++ [.scalar xi]
  let z := fs.squeeze t
  let t := t ++ [.scalar z]
  -- per IPA round: (Lⱼ, Rⱼ) → uⱼ
  let ipaRes := (List.finRange shape.k).foldl (fun (st : List (TranscriptElt F G) × List F) j =>
      let t := st.1 ++ [TranscriptElt.point (ps.ipaRounds j).1, TranscriptElt.point (ps.ipaRounds j).2]
      let uj := fs.squeeze t
      (t ++ [TranscriptElt.scalar uj], st.2 ++ [uj])) (t, [])
  { theta := theta, beta := beta, gamma := gamma, y := y, x := x,
    x1 := x1, x2 := x2, x3 := x3, x4 := x4, xi := xi, z := z,
    ipaRound := fun j => ipaRes.2.getD j.val 0 }

/-- The deployed (non-interactive) verifier's fingerprint MSM: `assembleFinalMsm` at the Fiat-Shamir
challenges. `grouped` is the `construct_intermediate_sets` output (see `Zcash.Snark.assembleQueries`).
The Fiat-Shamir assumption (the random-oracle step) is what carries the interactive verifier's
soundness to this non-interactive MSM. -/
def nonInteractiveFingerprint {shape : Shape} {F G : Type*} [Field F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G)
    (grouped : MultiopenGrouped shape.k F G) : Msm shape.k F G :=
  assembleFinalMsm ps (deriveChallenges fs init ps) grouped

end Zcash.Snark
