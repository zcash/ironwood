import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Core.ProofString
import Zcash.Snark.Core.Challenges
import Zcash.Snark.Verifier.Assemble

/-!
# Fiat–Shamir challenge schedule

The deployed verifier derives each challenge by hashing the transcript absorbed so far. This module
models halo2's Blake2b hash as the abstract `FiatShamir.squeeze`; it does not formalize Blake2b.
Reprogramming and uniform-challenge results live in `Soundness.Oracle.Model`.

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

/-- Public-instance commitments in Halo2's deployed proof-major, column-major absorb order. -/
def absorbInstanceCommitments {shape : Shape} {F G : Type*}
    (instanceCommitment : Fin shape.numProofs → ℕ → G) : List (TranscriptElt F G) :=
  (List.ofFn fun p : Fin shape.numProofs =>
    List.ofFn fun column : Fin shape.numInstanceColumns =>
      TranscriptElt.point (instanceCommitment p column)).flatten

/-- Instance-commitment absorption depends only on the configured proof/column rectangle. -/
theorem absorbInstanceCommitments_congr
    {shape : Shape} {F G : Type*}
    (instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G)
    (h : ∀ p (column : Fin shape.numInstanceColumns),
      instanceCommitment p column = instanceCommitment' p column) :
    absorbInstanceCommitments (F := F) instanceCommitment =
      absorbInstanceCommitments instanceCommitment' := by
  unfold absorbInstanceCommitments
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  apply congrArg List.ofFn
  funext column
  rw [h p column]

/-- The complete verifier-controlled Fiat–Shamir prefix: the VK transcript representation followed
by every configured public-instance commitment. -/
def initialTranscript {shape : Shape} {F G : Type*} (vkTranscriptRepr : F)
    (instanceCommitment : Fin shape.numProofs → ℕ → G) : List (TranscriptElt F G) :=
  TranscriptElt.scalar vkTranscriptRepr :: absorbInstanceCommitments instanceCommitment

/-- The canonical prefix is extensional over its configured instance commitments. -/
theorem initialTranscript_congr
    {shape : Shape} {F G : Type*} (vkTranscriptRepr : F)
    (instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G)
    (h : ∀ p (column : Fin shape.numInstanceColumns),
      instanceCommitment p column = instanceCommitment' p column) :
    initialTranscript vkTranscriptRepr instanceCommitment =
      initialTranscript vkTranscriptRepr instanceCommitment' := by
  simp only [initialTranscript, List.cons.injEq, true_and]
  exact absorbInstanceCommitments_congr instanceCommitment instanceCommitment' h

@[simp] theorem initialTranscript_head? {shape : Shape} {F G : Type*}
    (vkTranscriptRepr : F) (instanceCommitment : Fin shape.numProofs → ℕ → G) :
    (initialTranscript vkTranscriptRepr instanceCommitment).head? =
      some (TranscriptElt.scalar vkTranscriptRepr) := by
  rfl

@[simp] theorem initialTranscript_drop_one {shape : Shape} {F G : Type*}
    (vkTranscriptRepr : F) (instanceCommitment : Fin shape.numProofs → ℕ → G) :
    (initialTranscript vkTranscriptRepr instanceCommitment).drop 1 =
      absorbInstanceCommitments instanceCommitment := by
  rfl

@[simp] theorem absorbInstanceCommitments_length {shape : Shape} {F G : Type*}
    (instanceCommitment : Fin shape.numProofs → ℕ → G) :
    (absorbInstanceCommitments (F := F) instanceCommitment).length =
      shape.numProofs * shape.numInstanceColumns := by
  simp [absorbInstanceCommitments, List.length_flatten, List.sum_ofFn]

@[simp] theorem initialTranscript_length {shape : Shape} {F G : Type*}
    (vkTranscriptRepr : F) (instanceCommitment : Fin shape.numProofs → ℕ → G) :
    (initialTranscript vkTranscriptRepr instanceCommitment).length =
      1 + shape.numProofs * shape.numInstanceColumns := by
  simp [initialTranscript, Nat.add_comm]

theorem instanceCommitment_mem_initialTranscript {shape : Shape} {F G : Type*}
    (vkTranscriptRepr : F) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (p : Fin shape.numProofs) (column : Fin shape.numInstanceColumns) :
    TranscriptElt.point (instanceCommitment p column) ∈
      initialTranscript vkTranscriptRepr instanceCommitment := by
  simp [initialTranscript, absorbInstanceCommitments]

/-- Equality of canonical verifier prefixes pins the verifying-key transcript representation. -/
theorem vkTranscriptRepr_eq_of_initialTranscript_eq
    {shape : Shape} {F G : Type*}
    (vkTranscriptRepr vkTranscriptRepr' : F)
    (instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G)
    (hinit : initialTranscript vkTranscriptRepr instanceCommitment =
      initialTranscript vkTranscriptRepr' instanceCommitment') :
    vkTranscriptRepr = vkTranscriptRepr' := by
  have hscalar : TranscriptElt.scalar vkTranscriptRepr =
      TranscriptElt.scalar vkTranscriptRepr' :=
    (List.cons.inj hinit).1
  injection hscalar

/-- Generic mathematical implication from injectivity: equal canonical prefixes pin the verifying
key.  This utility is not a cryptographic hash assumption used by the adaptive-statement theorem.
Concrete cross-key binding is instead supplied by collision resistance of the deployed key hash;
captured fixtures may use a constant representation and receive only single-key faithfulness. -/
theorem vk_eq_of_initialTranscript_eq_of_injective
    {shape : Shape} {F G : Type*}
    (vkHash : VerifyingKey shape F G → F) (hinj : Function.Injective vkHash)
    (vk vk' : VerifyingKey shape F G)
    (instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G)
    (hinit : initialTranscript (vkHash vk) instanceCommitment =
      initialTranscript (vkHash vk') instanceCommitment') :
    vk = vk' :=
  hinj (vkTranscriptRepr_eq_of_initialTranscript_eq
    (vkHash vk) (vkHash vk') instanceCommitment instanceCommitment' hinit)

/-- Equality of canonical verifier prefixes pins every configured instance commitment. -/
theorem instanceCommitment_eq_of_initialTranscript_eq
    {shape : Shape} {F G : Type*}
    (vkTranscriptRepr vkTranscriptRepr' : F)
    (instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G)
    (hinit : initialTranscript vkTranscriptRepr instanceCommitment =
      initialTranscript vkTranscriptRepr' instanceCommitment')
    (p : Fin shape.numProofs) (column : Fin shape.numInstanceColumns) :
    instanceCommitment p column = instanceCommitment' p column := by
  have hflatten : absorbInstanceCommitments (F := F) instanceCommitment =
      absorbInstanceCommitments instanceCommitment' := by
    exact List.cons.inj hinit |>.2
  have chunks_injective : ∀ (xs ys : List (List (TranscriptElt F G))),
      xs.length = ys.length →
      (∀ row ∈ xs, row.length = shape.numInstanceColumns) →
      (∀ row ∈ ys, row.length = shape.numInstanceColumns) →
      xs.flatten = ys.flatten → xs = ys := by
    intro xs
    induction xs with
    | nil =>
        intro ys hlen _ _ _
        simpa using hlen.symm
    | cons x xs ih =>
        intro ys hlen hx hy hflat
        cases ys with
        | nil => simp at hlen
        | cons y ys =>
            have hxyLength : x.length = y.length := by
              rw [hx x (by simp), hy y (by simp)]
            have htotalLength := congrArg List.length hflat
            have htailFlattenLength : xs.flatten.length = ys.flatten.length := by
              simp only [List.flatten_cons, List.length_append] at htotalLength
              omega
            have hparts := List.append_inj' hflat htailFlattenLength
            have htailLength : xs.length = ys.length := by simpa using hlen
            have htail : xs = ys := ih ys htailLength
              (by intro row hrow; exact hx row (by simp [hrow]))
              (by intro row hrow; exact hy row (by simp [hrow])) hparts.2
            exact congrArg₂ List.cons hparts.1 htail
  let rows := List.ofFn fun p : Fin shape.numProofs =>
    List.ofFn fun column : Fin shape.numInstanceColumns =>
      TranscriptElt.point (F := F) (instanceCommitment p column)
  let rows' := List.ofFn fun p : Fin shape.numProofs =>
    List.ofFn fun column : Fin shape.numInstanceColumns =>
      TranscriptElt.point (F := F) (instanceCommitment' p column)
  have hrows : rows = rows' := by
    apply chunks_injective rows rows'
    · simp [rows, rows']
    · intro row hrow
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (show row ∈ rows from hrow)
      simp
    · intro row hrow
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (show row ∈ rows' from hrow)
      simp
    · simpa only [absorbInstanceCommitments, rows, rows'] using hflatten
  have hrowFunctions :
      (fun p : Fin shape.numProofs =>
        List.ofFn fun column : Fin shape.numInstanceColumns =>
          TranscriptElt.point (F := F) (instanceCommitment p column)) =
      (fun p : Fin shape.numProofs =>
        List.ofFn fun column : Fin shape.numInstanceColumns =>
          TranscriptElt.point (F := F) (instanceCommitment' p column)) :=
    List.ofFn_injective hrows
  have hcolumnsAt := congrFun hrowFunctions p
  have hcolumnFunctions :
      (fun column : Fin shape.numInstanceColumns =>
        TranscriptElt.point (F := F) (instanceCommitment p column)) =
      (fun column : Fin shape.numInstanceColumns =>
        TranscriptElt.point (F := F) (instanceCommitment' p column)) :=
    List.ofFn_injective hcolumnsAt
  simpa using TranscriptElt.point.inj (congrFun hcolumnFunctions column)

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

/-- Derive challenges from the canonical verifier-controlled prefix.  This is the statement-bound
entry point; `deriveChallenges` remains the low-level schedule over an explicit prefix. -/
def deriveChallengesForStatement {shape : Shape} {F G : Type*} [Zero F]
    (fs : FiatShamir F G) (vkTranscriptRepr : F)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) : Challenges shape.k F :=
  deriveChallenges fs (initialTranscript vkTranscriptRepr instanceCommitment) ps

/-- Statement-bound challenge derivation is extensional over the configured instance commitments. -/
theorem deriveChallengesForStatement_congr
    {shape : Shape} {F G : Type*} [Zero F]
    (fs : FiatShamir F G) (vkTranscriptRepr : F)
    (instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G)
    (h : ∀ p (column : Fin shape.numInstanceColumns),
      instanceCommitment p column = instanceCommitment' p column) :
    deriveChallengesForStatement fs vkTranscriptRepr instanceCommitment ps =
      deriveChallengesForStatement fs vkTranscriptRepr instanceCommitment' ps := by
  unfold deriveChallengesForStatement
  rw [initialTranscript_congr vkTranscriptRepr instanceCommitment instanceCommitment' h]

/-- The exact transcript presented to the first squeeze by the statement-bound verifier. -/
def preThetaTranscriptForStatement {shape : Shape} {F G : Type*}
    (vkTranscriptRepr : F) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) : List (TranscriptElt F G) :=
  initialTranscript vkTranscriptRepr instanceCommitment ++
    absorbPoints2 ps.adviceCommitments ++ [.challenge]

@[simp] theorem deriveChallengesForStatement_theta {shape : Shape} {F G : Type*} [Zero F]
    (fs : FiatShamir F G) (vkTranscriptRepr : F)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) :
    (deriveChallengesForStatement fs vkTranscriptRepr instanceCommitment ps).theta =
      fs.squeeze (preThetaTranscriptForStatement vkTranscriptRepr instanceCommitment ps) := by
  rfl

theorem vkTranscriptRepr_mem_preThetaTranscriptForStatement
    {shape : Shape} {F G : Type*} (vkTranscriptRepr : F)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) :
    TranscriptElt.scalar vkTranscriptRepr ∈
      preThetaTranscriptForStatement vkTranscriptRepr instanceCommitment ps := by
  simp [preThetaTranscriptForStatement, initialTranscript]

theorem instanceCommitment_mem_preThetaTranscriptForStatement
    {shape : Shape} {F G : Type*} (vkTranscriptRepr : F)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (p : Fin shape.numProofs)
    (column : Fin shape.numInstanceColumns) :
    TranscriptElt.point (instanceCommitment p column) ∈
      preThetaTranscriptForStatement vkTranscriptRepr instanceCommitment ps := by
  apply List.mem_append_left
  apply List.mem_append_left
  exact instanceCommitment_mem_initialTranscript vkTranscriptRepr instanceCommitment p column

theorem adviceCommitment_mem_preThetaTranscriptForStatement
    {shape : Shape} {F G : Type*} (vkTranscriptRepr : F)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (p : Fin shape.numProofs)
    (column : Fin shape.numAdviceColumns) :
    TranscriptElt.point (ps.adviceCommitments p column) ∈
      preThetaTranscriptForStatement vkTranscriptRepr instanceCommitment ps := by
  simp [preThetaTranscriptForStatement, absorbPoints2, absorbPoints]

/-- The deployed verifier's fingerprint MSM: `assemble` at the Fiat–Shamir challenges.

The random-oracle assumption is what transfers interactive soundness to this non-interactive MSM. -/
def nonInteractiveFingerprint {shape : Shape} {F G : Type*} [Field F] [DecidableEq F] [DecidableEq G]
    [Inhabited G] (fs : FiatShamir F G) (init : List (TranscriptElt F G))
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) : Msm shape.k F G :=
  assemble vk instanceCommitment ps (deriveChallenges fs init ps)

/-- The deployed verifier fingerprint with the VK and public statement bound into Fiat–Shamir. -/
def nonInteractiveFingerprintForStatement {shape : Shape} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (fs : FiatShamir F G) (vkHash : VerifyingKey shape F G → F) (vk : VerifyingKey shape F G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) : Msm shape.k F G :=
  assemble vk instanceCommitment ps
    (deriveChallengesForStatement fs (vkHash vk) instanceCommitment ps)

end Zcash.Snark
