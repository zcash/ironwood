import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Arithmetic
import Zcash.Arithmetic.Msm
import Zcash.Snark.Verifier.Assemble

/-!
# The fingerprint sample space

The quantified match (`Fingerprint/Epsilon.lean`) bounds counting fractions over one
product sample space: every `F_p`-valued proof-string slot and every challenge is an independent
uniform coordinate. This module gives that space a structured index:

* `ScalarSlot shape` — one constructor per scalar coordinate: the ten `F`-valued `ProofString`
  field families and the challenges. Group-valued slots are deliberately absent — commitments
  enter the assembled MSM only as bases, never as coefficient inputs
  (`Point.toProofString` holds them fixed). The last permutation set's absent `lastEval` is baked
  into the type (`permLastEval` indexes the non-last sets only), so a uniform assignment
  corresponds exactly to a uniform well-formed scalar read stream — no constant phantom
  coordinate.
* `Point shape` — an assignment of the coordinates, `ScalarSlot shape → F_p`. A point of the
  sample space *is* such an assignment; no bundling.
* `Point.toProofString` / `Point.toChallenges` — rebuild verifier inputs from an assignment,
  holding a template's group-valued fields fixed. Every point satisfies the deployed read
  schedule by construction (`proofStringWellFormed_toProofString`).
* `Point.ofInputs` — read an assignment off concrete inputs; the roundtrip lemmas rewrite
  fixture statements at captured `(ps, ch)` pairs into `Point` form.
* `IsChallengeSlot` / `Point.merge` — the challenge/slot partition of the coordinates and the
  merge of one assignment per side into a point: the frame in which the challenge-restricted
  ε theorem fixes the proof-string slots and counts over the challenges alone.
* `MsmCoord` / `Msm.coeffAt` — positional coordinates for the assembled MSM's coefficients: the
  index set of the coefficient families the ε theorem compares.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

/-- One scalar coordinate of the fingerprint sample space: an `F_p`-valued proof-string slot or a
challenge, in the verifier's read order (`ProofString`, then `Challenges` in squeeze order). The
five `lookup*Eval` families are `LookupEval`'s fields; `permEval`/`permNextEval`/`permLastEval`
are `PermSetEval`'s, with `permLastEval` indexing only the non-last sets — the last set's
`lastEval` is absent from the deployed read schedule (`permutationLastEvalsWellFormed`), so it is
absent from the type. -/
inductive ScalarSlot (shape : Shape) where
  | instanceEval (p : Fin shape.numProofs) (q : Fin shape.numInstanceQueries)
  | adviceEval (p : Fin shape.numProofs) (q : Fin shape.numAdviceQueries)
  | fixedEval (q : Fin shape.numFixedQueries)
  | vanishingRandomEval
  | permCommonEval (c : Fin shape.numPermutationColumns)
  | permEval (p : Fin shape.numProofs) (s : Fin shape.numPermutationSets)
  | permNextEval (p : Fin shape.numProofs) (s : Fin shape.numPermutationSets)
  | permLastEval (p : Fin shape.numProofs) (s : Fin (shape.numPermutationSets - 1))
  | lookupProductEval (p : Fin shape.numProofs) (l : Fin shape.numLookups)
  | lookupProductNextEval (p : Fin shape.numProofs) (l : Fin shape.numLookups)
  | lookupPermInputEval (p : Fin shape.numProofs) (l : Fin shape.numLookups)
  | lookupPermInputInvEval (p : Fin shape.numProofs) (l : Fin shape.numLookups)
  | lookupPermTableEval (p : Fin shape.numProofs) (l : Fin shape.numLookups)
  | multiopenU (u : Fin shape.numPointSets)
  | ipaC
  | ipaF
  | theta
  | beta
  | gamma
  | y
  | x
  | x1
  | x2
  | x3
  | x4
  | xi
  | z
  | ipaRound (j : Fin shape.k)
deriving DecidableEq, Fintype

/-- `true` exactly on the twelve challenge coordinates — the constructors `Point.toChallenges`
reads; `false` on the proof-string slot families `Point.toProofString` reads. -/
def isChallengeSlot {shape : Shape} : ScalarSlot shape → Bool
  | .theta | .beta | .gamma | .y | .x | .x1 | .x2 | .x3 | .x4 | .xi | .z | .ipaRound _ => true
  | _ => false

/-- The challenge side of the sample-space partition: a coordinate the verifier squeezes rather
than reads off the proof string. The challenge-restricted ε theorem
(`Fingerprint/Epsilon.lean`) fixes the slot side and counts over these coordinates alone. -/
def IsChallengeSlot {shape : Shape} (v : ScalarSlot shape) : Prop :=
  isChallengeSlot v = true

instance {shape : Shape} : DecidablePred (IsChallengeSlot (shape := shape)) := fun v =>
  inferInstanceAs (Decidable (isChallengeSlot v = true))

/-- A point of the fingerprint sample space: an assignment of every scalar coordinate. -/
abbrev Point (shape : Shape) := ScalarSlot shape → Fp

/-- Read the challenges off an assignment, in squeeze order. -/
def Point.toChallenges {shape : Shape} (pt : Point shape) : Challenges shape.k Fp where
  theta := pt .theta
  beta := pt .beta
  gamma := pt .gamma
  y := pt .y
  x := pt .x
  x1 := pt .x1
  x2 := pt .x2
  x3 := pt .x3
  x4 := pt .x4
  xi := pt .xi
  z := pt .z
  ipaRound := fun j => pt (.ipaRound j)

/-- Rebuild a proof string from an assignment, holding the template's ten group-valued fields
fixed. Every scalar field reads the assignment; `lastEval` is `some` exactly on the non-last
sets, so the result follows the deployed read schedule at every point
(`proofStringWellFormed_toProofString`). The assembled coefficients therefore depend on the
template only through its group data — bases, never coefficients. -/
def Point.toProofString {shape : Shape} {G : Type*} (pt : Point shape)
    (base : ProofString shape Fp G) : ProofString shape Fp G where
  adviceCommitments := base.adviceCommitments
  lookupPermutedInput := base.lookupPermutedInput
  lookupPermutedTable := base.lookupPermutedTable
  permutationProduct := base.permutationProduct
  lookupProduct := base.lookupProduct
  vanishingRandom := base.vanishingRandom
  hPieces := base.hPieces
  instanceEvals := fun p q => pt (.instanceEval p q)
  adviceEvals := fun p q => pt (.adviceEval p q)
  fixedEvals := fun q => pt (.fixedEval q)
  vanishingRandomEval := pt .vanishingRandomEval
  permutationCommonEvals := fun c => pt (.permCommonEval c)
  permutationSetEvals := fun p s =>
    { eval := pt (.permEval p s)
      nextEval := pt (.permNextEval p s)
      lastEval :=
        if h : s.val + 1 < shape.numPermutationSets then
          some (pt (.permLastEval p ⟨s.val, by omega⟩))
        else
          none }
  lookupEvals := fun p l =>
    { productEval := pt (.lookupProductEval p l)
      productNextEval := pt (.lookupProductNextEval p l)
      permutedInputEval := pt (.lookupPermInputEval p l)
      permutedInputInvEval := pt (.lookupPermInputInvEval p l)
      permutedTableEval := pt (.lookupPermTableEval p l) }
  multiopenQPrime := base.multiopenQPrime
  multiopenU := fun u => pt (.multiopenU u)
  ipaS := base.ipaS
  ipaRounds := base.ipaRounds
  ipaC := pt .ipaC
  ipaF := pt .ipaF

/-- Read an assignment off concrete verifier inputs. The `permLastEval` slots read through
`Option.getD`; on well-formed proof strings the `some` is always present at the indexed
(non-last) sets, so the roundtrip `toProofString_ofInputs` recovers the input exactly. -/
def Point.ofInputs {shape : Shape} {G : Type*} (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Point shape
  | .instanceEval p q => ps.instanceEvals p q
  | .adviceEval p q => ps.adviceEvals p q
  | .fixedEval q => ps.fixedEvals q
  | .vanishingRandomEval => ps.vanishingRandomEval
  | .permCommonEval c => ps.permutationCommonEvals c
  | .permEval p s => (ps.permutationSetEvals p s).eval
  | .permNextEval p s => (ps.permutationSetEvals p s).nextEval
  | .permLastEval p s => ((ps.permutationSetEvals p ⟨s.val, by omega⟩).lastEval).getD 0
  | .lookupProductEval p l => (ps.lookupEvals p l).productEval
  | .lookupProductNextEval p l => (ps.lookupEvals p l).productNextEval
  | .lookupPermInputEval p l => (ps.lookupEvals p l).permutedInputEval
  | .lookupPermInputInvEval p l => (ps.lookupEvals p l).permutedInputInvEval
  | .lookupPermTableEval p l => (ps.lookupEvals p l).permutedTableEval
  | .multiopenU u => ps.multiopenU u
  | .ipaC => ps.ipaC
  | .ipaF => ps.ipaF
  | .theta => ch.theta
  | .beta => ch.beta
  | .gamma => ch.gamma
  | .y => ch.y
  | .x => ch.x
  | .x1 => ch.x1
  | .x2 => ch.x2
  | .x3 => ch.x3
  | .x4 => ch.x4
  | .xi => ch.xi
  | .z => ch.z
  | .ipaRound j => ch.ipaRound j

/-- Merge a proof-string slot assignment with a challenge assignment into a full sample-space
point: challenge coordinates read `g`, slot coordinates read `slotVals`. The
challenge-restricted ε theorem counts merged points over `g` alone. -/
def Point.merge {shape : Shape}
    (slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp)
    (g : {v : ScalarSlot shape // IsChallengeSlot v} → Fp) : Point shape := fun v =>
  if h : IsChallengeSlot v then g ⟨v, h⟩ else slotVals ⟨v, h⟩

/-- A merged point reads the challenge assignment at a challenge coordinate. -/
theorem Point.merge_apply_pos {shape : Shape}
    {slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp}
    {g : {v : ScalarSlot shape // IsChallengeSlot v} → Fp} {v : ScalarSlot shape}
    (h : IsChallengeSlot v) : Point.merge slotVals g v = g ⟨v, h⟩ :=
  dif_pos h

/-- A merged point reads the slot assignment at a proof-string slot coordinate. -/
theorem Point.merge_apply_neg {shape : Shape}
    {slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp}
    {g : {v : ScalarSlot shape // IsChallengeSlot v} → Fp} {v : ScalarSlot shape}
    (h : ¬ IsChallengeSlot v) : Point.merge slotVals g v = slotVals ⟨v, h⟩ :=
  dif_neg h

@[simp] theorem Point.merge_challenge {shape : Shape}
    {slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp}
    {g : {v : ScalarSlot shape // IsChallengeSlot v} → Fp}
    (w : {v : ScalarSlot shape // IsChallengeSlot v}) :
    Point.merge slotVals g w.val = g w := by
  rw [Point.merge_apply_pos w.property]

@[simp] theorem Point.merge_slot {shape : Shape}
    {slotVals : {v : ScalarSlot shape // ¬ IsChallengeSlot v} → Fp}
    {g : {v : ScalarSlot shape // IsChallengeSlot v} → Fp}
    (w : {v : ScalarSlot shape // ¬ IsChallengeSlot v}) :
    Point.merge slotVals g w.val = slotVals w := by
  rw [Point.merge_apply_neg w.property]

/-- Splitting a point along the partition and re-merging recovers it, so facts at a concrete
point — a captured point's good-event membership, say — read verbatim in the merged frame. -/
theorem Point.merge_restrict {shape : Shape} (pt : Point shape) :
    Point.merge (fun v => pt v.val) (fun v => pt v.val) = pt := by
  funext v
  unfold Point.merge
  split <;> rfl

section ReadBack

variable {shape : Shape} {G : Type*} (pt : Point shape) (base : ProofString shape Fp G)

@[simp] theorem toChallenges_theta : pt.toChallenges.theta = pt .theta := rfl
@[simp] theorem toChallenges_beta : pt.toChallenges.beta = pt .beta := rfl
@[simp] theorem toChallenges_gamma : pt.toChallenges.gamma = pt .gamma := rfl
@[simp] theorem toChallenges_y : pt.toChallenges.y = pt .y := rfl
@[simp] theorem toChallenges_x : pt.toChallenges.x = pt .x := rfl
@[simp] theorem toChallenges_x1 : pt.toChallenges.x1 = pt .x1 := rfl
@[simp] theorem toChallenges_x2 : pt.toChallenges.x2 = pt .x2 := rfl
@[simp] theorem toChallenges_x3 : pt.toChallenges.x3 = pt .x3 := rfl
@[simp] theorem toChallenges_x4 : pt.toChallenges.x4 = pt .x4 := rfl
@[simp] theorem toChallenges_xi : pt.toChallenges.xi = pt .xi := rfl
@[simp] theorem toChallenges_z : pt.toChallenges.z = pt .z := rfl
@[simp] theorem toChallenges_ipaRound (j : Fin shape.k) :
    pt.toChallenges.ipaRound j = pt (.ipaRound j) := rfl

@[simp] theorem toProofString_adviceCommitments :
    (pt.toProofString base).adviceCommitments = base.adviceCommitments := rfl
@[simp] theorem toProofString_lookupPermutedInput :
    (pt.toProofString base).lookupPermutedInput = base.lookupPermutedInput := rfl
@[simp] theorem toProofString_lookupPermutedTable :
    (pt.toProofString base).lookupPermutedTable = base.lookupPermutedTable := rfl
@[simp] theorem toProofString_permutationProduct :
    (pt.toProofString base).permutationProduct = base.permutationProduct := rfl
@[simp] theorem toProofString_lookupProduct :
    (pt.toProofString base).lookupProduct = base.lookupProduct := rfl
@[simp] theorem toProofString_vanishingRandom :
    (pt.toProofString base).vanishingRandom = base.vanishingRandom := rfl
@[simp] theorem toProofString_hPieces :
    (pt.toProofString base).hPieces = base.hPieces := rfl
@[simp] theorem toProofString_multiopenQPrime :
    (pt.toProofString base).multiopenQPrime = base.multiopenQPrime := rfl
@[simp] theorem toProofString_ipaS : (pt.toProofString base).ipaS = base.ipaS := rfl
@[simp] theorem toProofString_ipaRounds :
    (pt.toProofString base).ipaRounds = base.ipaRounds := rfl

@[simp] theorem toProofString_instanceEvals (p : Fin shape.numProofs)
    (q : Fin shape.numInstanceQueries) :
    (pt.toProofString base).instanceEvals p q = pt (.instanceEval p q) := rfl
@[simp] theorem toProofString_adviceEvals (p : Fin shape.numProofs)
    (q : Fin shape.numAdviceQueries) :
    (pt.toProofString base).adviceEvals p q = pt (.adviceEval p q) := rfl
@[simp] theorem toProofString_fixedEvals (q : Fin shape.numFixedQueries) :
    (pt.toProofString base).fixedEvals q = pt (.fixedEval q) := rfl
@[simp] theorem toProofString_vanishingRandomEval :
    (pt.toProofString base).vanishingRandomEval = pt .vanishingRandomEval := rfl
@[simp] theorem toProofString_permutationCommonEvals (c : Fin shape.numPermutationColumns) :
    (pt.toProofString base).permutationCommonEvals c = pt (.permCommonEval c) := rfl
@[simp] theorem toProofString_multiopenU (u : Fin shape.numPointSets) :
    (pt.toProofString base).multiopenU u = pt (.multiopenU u) := rfl
@[simp] theorem toProofString_ipaC : (pt.toProofString base).ipaC = pt .ipaC := rfl
@[simp] theorem toProofString_ipaF : (pt.toProofString base).ipaF = pt .ipaF := rfl

@[simp] theorem toProofString_permEval (p : Fin shape.numProofs)
    (s : Fin shape.numPermutationSets) :
    ((pt.toProofString base).permutationSetEvals p s).eval = pt (.permEval p s) := rfl
@[simp] theorem toProofString_permNextEval (p : Fin shape.numProofs)
    (s : Fin shape.numPermutationSets) :
    ((pt.toProofString base).permutationSetEvals p s).nextEval = pt (.permNextEval p s) := rfl

theorem toProofString_permLastEval_of_lt (p : Fin shape.numProofs)
    (s : Fin shape.numPermutationSets) (h : s.val + 1 < shape.numPermutationSets) :
    ((pt.toProofString base).permutationSetEvals p s).lastEval
      = some (pt (.permLastEval p ⟨s.val, by omega⟩)) := by
  simp [Point.toProofString, h]

theorem toProofString_permLastEval_of_last (p : Fin shape.numProofs)
    (s : Fin shape.numPermutationSets) (h : s.val + 1 = shape.numPermutationSets) :
    ((pt.toProofString base).permutationSetEvals p s).lastEval = none := by
  simp [Point.toProofString, show ¬ s.val + 1 < shape.numPermutationSets by omega]

@[simp] theorem toProofString_lookupProductEval (p : Fin shape.numProofs)
    (l : Fin shape.numLookups) :
    ((pt.toProofString base).lookupEvals p l).productEval = pt (.lookupProductEval p l) := rfl
@[simp] theorem toProofString_lookupProductNextEval (p : Fin shape.numProofs)
    (l : Fin shape.numLookups) :
    ((pt.toProofString base).lookupEvals p l).productNextEval
      = pt (.lookupProductNextEval p l) := rfl
@[simp] theorem toProofString_lookupPermInputEval (p : Fin shape.numProofs)
    (l : Fin shape.numLookups) :
    ((pt.toProofString base).lookupEvals p l).permutedInputEval
      = pt (.lookupPermInputEval p l) := rfl
@[simp] theorem toProofString_lookupPermInputInvEval (p : Fin shape.numProofs)
    (l : Fin shape.numLookups) :
    ((pt.toProofString base).lookupEvals p l).permutedInputInvEval
      = pt (.lookupPermInputInvEval p l) := rfl
@[simp] theorem toProofString_lookupPermTableEval (p : Fin shape.numProofs)
    (l : Fin shape.numLookups) :
    ((pt.toProofString base).lookupEvals p l).permutedTableEval
      = pt (.lookupPermTableEval p l) := rfl

end ReadBack

/-- The read-schedule check, unfolded to its per-set content: the last set's `lastEval` is
`none`, every other set's is `some`. -/
theorem permutationLastEvalsWellFormed_iff {shape : Shape} {F G : Type*}
    (ps : ProofString shape F G) :
    permutationLastEvalsWellFormed ps = true ↔
      ∀ (p : Fin shape.numProofs) (s : Fin shape.numPermutationSets),
        if s.val + 1 = shape.numPermutationSets then
          (ps.permutationSetEvals p s).lastEval = none
        else
          (ps.permutationSetEvals p s).lastEval ≠ none := by
  simp only [permutationLastEvalsWellFormed, List.all_eq_true, List.mem_ofFn, id_eq,
    forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · intro h p s
    have hs := h p s
    split at hs <;> split <;> try omega
    · cases hE : (ps.permutationSetEvals p s).lastEval with
      | none => rfl
      | some v => rw [hE] at hs; exact absurd hs (by simp)
    · cases hE : (ps.permutationSetEvals p s).lastEval with
      | none => rw [hE] at hs; exact absurd hs (by simp)
      | some v => simp
  · intro h p s
    have hs := h p s
    split at hs <;> split <;> try omega
    · rw [hs]
    · cases hE : (ps.permutationSetEvals p s).lastEval with
      | none => exact absurd hE hs
      | some v => rfl

/-- Every point of the sample space yields a well-formed proof string: the read-schedule shape is
baked into `ScalarSlot`, so `assemble?`'s first gate passes on the whole space. -/
@[simp] theorem proofStringWellFormed_toProofString {shape : Shape} {G : Type*}
    (pt : Point shape) (base : ProofString shape Fp G) :
    proofStringWellFormed (pt.toProofString base) = true := by
  rw [proofStringWellFormed, permutationLastEvalsWellFormed_iff]
  intro p s
  by_cases hlast : s.val + 1 = shape.numPermutationSets
  · rw [if_pos hlast]
    exact toProofString_permLastEval_of_last pt base p s hlast
  · have hs := s.isLt
    rw [if_neg hlast, toProofString_permLastEval_of_lt pt base p s (by omega)]
    simp

/-- Reading the challenges back off `Point.ofInputs` recovers the input challenges exactly. -/
@[simp] theorem toChallenges_ofInputs {shape : Shape} {G : Type*} (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : (Point.ofInputs ps ch).toChallenges = ch := rfl

/-- Rebuilding a well-formed proof string from its own assignment recovers it exactly: the
`Option.getD` in `Point.ofInputs` is always applied to a `some` at the indexed sets. -/
theorem toProofString_ofInputs {shape : Shape} {G : Type*} (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (hwf : proofStringWellFormed ps = true) :
    (Point.ofInputs ps ch).toProofString ps = ps := by
  rw [proofStringWellFormed, permutationLastEvalsWellFormed_iff] at hwf
  obtain ⟨ac, lpi, lpt, pp, lp, vr, hp, ie, ae, fe, vre, pce, pse, le, mq, mu, is, ir, ic, ipf⟩ :=
    ps
  simp only [Point.toProofString, Point.ofInputs, ProofString.mk.injEq, and_true, true_and]
  funext p s
  have hs := hwf p s
  by_cases hlast : s.val + 1 = shape.numPermutationSets
  · rw [if_pos hlast] at hs
    have hnlt : ¬ s.val + 1 < shape.numPermutationSets := by omega
    simp only [dif_neg hnlt]
    rcases hE : pse p s with ⟨e, ne, l⟩
    simp only [hE] at hs
    simp_all
  · rw [if_neg hlast] at hs
    have hsl := s.isLt
    have hlt : s.val + 1 < shape.numPermutationSets := by omega
    simp only [dif_pos hlt]
    rcases hE : pse p s with ⟨e, ne, l⟩
    cases l with
    | none => simp only [hE] at hs; simp at hs
    | some v => rfl

/-- A coefficient position of the assembled MSM: a URS `g`-scalar, the `w`/`u` scalars, or the
`t`-th `other`-term coefficient of a term list of length `L`. The good event pins the assembled
`other` length to a fixed `L`, making these a complete, fixed index set for the coefficient
family the ε theorem compares. -/
inductive MsmCoord (k L : ℕ) where
  | g (i : Fin (2 ^ k))
  | w
  | u
  | term (t : Fin L)
deriving DecidableEq, Fintype

/-- The coefficient at a coordinate; `term t` reads coefficient `t` of `other`, defaulting to `0`
past the end (unreachable when the term list has length `L`). -/
def _root_.Zcash.Arithmetic.Msm.coeffAt {k L : ℕ} {F G : Type*} [Zero F]
    (m : Msm k F G) : MsmCoord k L → F
  | .g i => m.gScalars i
  | .w => m.wScalar
  | .u => m.uScalar
  | .term t => (m.other.map Prod.fst).getD t.val 0

end Zcash.Snark
