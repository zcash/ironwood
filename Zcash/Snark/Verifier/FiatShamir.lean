import Mathlib.Tactic
import Zcash.Snark.Core.ProofString
import Zcash.Snark.Core.Challenges
import Zcash.Snark.Verifier.Assemble

/-!
# Fiat–Shamir challenge schedule

The deployed verifier derives each challenge by hashing the transcript absorbed so far. This module
models halo2's Blake2b hash as the abstract `FiatShamir.squeeze`; it does not formalize Blake2b.
Reprogramming and uniform-challenge results live in `Soundness.FiatShamir.Oracle`.

`deriveChallenges` records the absorb/squeeze order from halo2's PLONK, multiopen, and commitment
verifiers. `nonInteractiveFingerprint` runs `assemble` at those derived challenges.

The security development idealizes `squeeze` as a random oracle; identifying deployed Blake2b and
field conversion with it is external. Fixtures use trusted typed captures, not transcript bytes.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

/-- A point, scalar, or challenge-domain marker written to the Fiat–Shamir transcript.

The constructors correspond to halo2's three Blake2b domain prefixes. A squeeze absorbs `challenge`;
it does not feed the resulting field element back into the transcript. -/
inductive TranscriptElt (F G : Type*) where
  | point : G → TranscriptElt F G
  | scalar : F → TranscriptElt F G
  | challenge : TranscriptElt F G
  deriving DecidableEq

/-- The abstract Fiat–Shamir hash: squeeze a field challenge from the absorbed transcript.

The deployed hash is Blake2b. The model treats it as a random oracle; the querying adversary,
query loss, and Blake2b justification remain outside this structure. -/
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

/-- Derive the verifier's challenges in halo2's deployed absorb/squeeze order.

Each squeeze first appends `TranscriptElt.challenge`; the result is not re-absorbed. `init` contains
the verifying-key hash and instance commitments absorbed before the proof. -/
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

/-- The deployed verifier's fingerprint MSM: `assemble` at the Fiat–Shamir challenges.

The random-oracle assumption is what transfers interactive soundness to this non-interactive MSM. -/
def nonInteractiveFingerprint {shape : Shape} {F G : Type*} [Field F] [DecidableEq F]
    [Inhabited G] (fs : FiatShamir F G) (init : List (TranscriptElt F G))
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) : Msm shape.k F G :=
  assemble vk instanceCommitment ps (deriveChallenges fs init ps)

end Zcash.Snark
