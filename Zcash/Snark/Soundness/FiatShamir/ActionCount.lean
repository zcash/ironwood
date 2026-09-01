import Zcash.Snark.Soundness.FiatShamir.Ordering
import Zcash.Snark.Verifier.Transcript

/-!
# Fiat–Shamir separation across action counts

One Orchard proof covers a bundle of `n` Actions: the verifier absorbs `n` instance commitments
and `n` sets of advice commitments before its first squeeze. This module proves that challenge
derivations at two different action counts never share an oracle query — at the typed level, and
at the byte level beneath it.

* `deriveChallenges_congr_of_agree_on_cone` — **oracle locality**: the schedule only ever queries
  transcripts that extend its pre-`θ` prefix, so two oracles agreeing on that cone derive the
  same challenges.
* `preTheta_not_prefix_of_numProofs_lt` — pre-`θ` prefixes at different action counts are
  prefix-incomparable: where the shorter one carries its challenge marker, the longer one is
  still absorbing a point. `preTheta_prefixFree_of_numProofs_ne` states both directions explicitly,
  and the two cones are therefore disjoint (`preTheta_cones_disjoint`).
* `encodeTranscript_prefixFree_of_numProofs_ne` and `encodeTranscript_cones_disjoint` — the same
  statements for the byte strings the deployed hash sees, by prefix reflection of the transcript
  encoding.
* `deriveChallenges_reprogram_other_count` — reprogramming the oracle anywhere on the `m`-action
  cone leaves every `n`-action challenge unchanged, for `n ≠ m`.

In the random-oracle model this is what "the `n`-action and `m`-action verifiers draw independent
challenges" means: their query sets are disjoint, so the oracle's answers on one carry no
information about the other. The only hypothesis beyond a shared circuit is that at least one
instance or advice column exists, which every real circuit satisfies.
-/

namespace Zcash.Snark

variable {F G : Type*}

/-! ## Oracle locality -/

/-- The first squeeze's input over an explicit prefix: the prefix, every advice commitment, and
the challenge marker. -/
def preThetaTranscript {shape : Shape} (init : List (TranscriptElt F G))
    (ps : ProofString shape F G) : List (TranscriptElt F G) :=
  init ++ absorbPoints2 ps.adviceCommitments ++ [.challenge]

/-- The statement-bound pre-`θ` transcript is the explicit-prefix form at `initialTranscript`. -/
theorem preThetaTranscriptForStatement_eq {shape : Shape} (vk : F)
    (inst : Fin shape.numProofs → ℕ → G) (ps : ProofString shape F G) :
    preThetaTranscriptForStatement vk inst ps = preThetaTranscript (initialTranscript vk inst) ps :=
  rfl

/-- **Oracle locality of the schedule.** Two oracles that agree on every transcript extending the
pre-`θ` prefix derive the same challenges: no squeeze of `deriveChallenges` looks outside that
cone. Stepped through in the body: every squeeze input, the IPA rounds included, is the pre-`θ`
prefix followed by later absorptions. -/
theorem deriveChallenges_congr_of_agree_on_cone {shape : Shape} [Zero F]
    (fs fs' : FiatShamir F G) (init : List (TranscriptElt F G)) (ps : ProofString shape F G)
    (h : ∀ t, preThetaTranscript init ps <+: t → fs.squeeze t = fs'.squeeze t) :
    deriveChallenges fs init ps = deriveChallenges fs' init ps := by
  -- The agreement, restated on the right-associated form every squeeze input normalizes to.
  have key : ∀ rest : List (TranscriptElt F G),
      fs.squeeze (init ++ (absorbPoints2 ps.adviceCommitments ++ (TranscriptElt.challenge :: rest)))
        = fs'.squeeze
          (init ++ (absorbPoints2 ps.adviceCommitments ++ (TranscriptElt.challenge :: rest))) := by
    intro rest
    apply h
    simp [preThetaTranscript]
  -- Expose the eleven named squeezes and the IPA fold's per-round squeezes.
  simp only [deriveChallenges]
  rw [ipaFold_challenges fs, ipaFold_challenges fs']
  simp only [List.append_assoc, List.cons_append, List.nil_append, key]

/-! ## The pre-`θ` prefix, element by element -/

/-- Every absorbed advice commitment is a point. -/
theorem absorbPoints2_mem_point {a b : ℕ} (f : Fin a → Fin b → G) {e : TranscriptElt F G}
    (he : e ∈ absorbPoints2 (F := F) f) : ∃ P, e = .point P := by
  simp only [absorbPoints2, absorbPoints, List.mem_flatten] at he
  obtain ⟨l, hl, hel⟩ := he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hel
  exact ⟨_, rfl⟩

/-- Every absorbed instance commitment is a point. -/
theorem absorbInstanceCommitments_mem_point {shape : Shape} (inst : Fin shape.numProofs → ℕ → G)
    {e : TranscriptElt F G} (he : e ∈ absorbInstanceCommitments (F := F) inst) :
    ∃ P, e = .point P := by
  simp only [absorbInstanceCommitments, List.mem_flatten] at he
  obtain ⟨l, hl, hel⟩ := he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hel
  exact ⟨_, rfl⟩

/-- A proof-major matrix of commitments absorbs one point per entry. -/
@[simp] theorem absorbPoints2_length {a b : ℕ} (f : Fin a → Fin b → G) :
    (absorbPoints2 (F := F) f).length = a * b := by
  simp [absorbPoints2, absorbPoints, List.length_flatten, List.map_ofFn, List.sum_ofFn]

/-- The instance and advice commitments the first squeeze covers, in absorb order. -/
def preThetaPoints {shape : Shape} (inst : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) : List (TranscriptElt F G) :=
  absorbInstanceCommitments inst ++ absorbPoints2 ps.adviceCommitments

/-- `n · c` instance commitments followed by `n · a` advice commitments. -/
theorem preThetaPoints_length {shape : Shape} (inst : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) :
    (preThetaPoints inst ps).length
      = shape.numProofs * shape.numInstanceColumns + shape.numProofs * shape.numAdviceColumns := by
  simp [preThetaPoints]

/-- Every commitment absorbed before the first squeeze is a point. -/
theorem preThetaPoints_mem_point {shape : Shape} (inst : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) {e : TranscriptElt F G} (he : e ∈ preThetaPoints inst ps) :
    ∃ P, e = .point P := by
  rcases List.mem_append.mp he with h | h
  · exact absorbInstanceCommitments_mem_point inst h
  · exact absorbPoints2_mem_point _ h

/-- The statement-bound pre-`θ` transcript is the key scalar, the commitment points, then the
challenge marker. -/
theorem preThetaTranscriptForStatement_eq_cons {shape : Shape} (vk : F)
    (inst : Fin shape.numProofs → ℕ → G) (ps : ProofString shape F G) :
    preThetaTranscriptForStatement vk inst ps
      = TranscriptElt.scalar vk :: (preThetaPoints inst ps ++ [.challenge]) := by
  simp [preThetaTranscriptForStatement, initialTranscript, preThetaPoints, List.append_assoc]

/-- The pre-`θ` transcript has `1 + n·(c + a) + 1` elements: key scalar, points, marker. -/
theorem preThetaTranscriptForStatement_length {shape : Shape} (vk : F)
    (inst : Fin shape.numProofs → ℕ → G) (ps : ProofString shape F G) :
    (preThetaTranscriptForStatement vk inst ps).length
      = 1 + (shape.numProofs * shape.numInstanceColumns
          + shape.numProofs * shape.numAdviceColumns) + 1 := by
  rw [preThetaTranscriptForStatement_eq_cons]
  simp [preThetaPoints_length]
  omega

/-- The challenge marker sits at index `1 + n·(c + a)`. -/
theorem preThetaTranscriptForStatement_getElem?_challenge {shape : Shape} (vk : F)
    (inst : Fin shape.numProofs → ℕ → G) (ps : ProofString shape F G) :
    (preThetaTranscriptForStatement vk inst ps)[1 + (shape.numProofs * shape.numInstanceColumns
        + shape.numProofs * shape.numAdviceColumns)]? = some .challenge := by
  rw [preThetaTranscriptForStatement_eq_cons, Nat.add_comm, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [preThetaPoints_length]), preThetaPoints_length,
    Nat.sub_self]
  rfl

/-- Every index strictly between the key scalar and the marker holds a point. -/
theorem preThetaTranscriptForStatement_getElem?_point {shape : Shape} (vk : F)
    (inst : Fin shape.numProofs → ℕ → G) (ps : ProofString shape F G) (i : ℕ) (h1 : 1 ≤ i)
    (h2 : i < 1 + (shape.numProofs * shape.numInstanceColumns
        + shape.numProofs * shape.numAdviceColumns)) :
    ∃ P, (preThetaTranscriptForStatement vk inst ps)[i]? = some (.point P) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j < (preThetaPoints inst ps).length := by rw [preThetaPoints_length]; omega
  rw [preThetaTranscriptForStatement_eq_cons, List.getElem?_cons_succ,
    List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
  obtain ⟨P, hP⟩ := preThetaPoints_mem_point inst ps (List.getElem_mem hj)
  exact ⟨P, by rw [hP]⟩

/-! ## Separation -/

/-- A prefix agrees with the list at every index it covers. -/
theorem getElem?_eq_of_prefix_of_lt {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : ℕ}
    (hi : i < l₁.length) : l₂[i]? = l₁[i]? := by
  obtain ⟨r, rfl⟩ := h
  rw [List.getElem?_append_left hi]

/-- **Pre-`θ` prefixes at different action counts are prefix-incomparable.** With `n < m`
actions of one circuit, the `n`-action prefix carries its challenge marker at index
`1 + n·(c + a)`, where the `m`-action prefix still absorbs a point. -/
theorem preTheta_not_prefix_of_numProofs_lt {shape shape' : Shape}
    (hc : shape.toCircuitShape = shape'.toCircuitShape)
    (hpos : 0 < shape.numInstanceColumns + shape.numAdviceColumns)
    (hlt : shape.numProofs < shape'.numProofs) (vk vk' : F)
    (inst : Fin shape.numProofs → ℕ → G) (inst' : Fin shape'.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ps' : ProofString shape' F G) :
    ¬ preThetaTranscriptForStatement vk inst ps <+: preThetaTranscriptForStatement vk' inst' ps' := by
  intro hpre
  have hcols : shape.numInstanceColumns = shape'.numInstanceColumns :=
    congrArg CircuitShape.numInstanceColumns hc
  have hadv : shape.numAdviceColumns = shape'.numAdviceColumns :=
    congrArg CircuitShape.numAdviceColumns hc
  have hmul : shape.numProofs * (shape.numInstanceColumns + shape.numAdviceColumns)
      < shape'.numProofs * (shape.numInstanceColumns + shape.numAdviceColumns) :=
    Nat.mul_lt_mul_of_pos_right hlt hpos
  rw [Nat.mul_add, Nat.mul_add] at hmul
  have hi : 1 + (shape.numProofs * shape.numInstanceColumns
      + shape.numProofs * shape.numAdviceColumns)
        < (preThetaTranscriptForStatement vk inst ps).length := by
    rw [preThetaTranscriptForStatement_length]; omega
  have hch := preThetaTranscriptForStatement_getElem?_challenge vk inst ps
  obtain ⟨P, hP⟩ := preThetaTranscriptForStatement_getElem?_point vk' inst' ps'
    (1 + (shape.numProofs * shape.numInstanceColumns + shape.numProofs * shape.numAdviceColumns))
    (by omega) (by rw [← hcols, ← hadv]; omega)
  rw [getElem?_eq_of_prefix_of_lt hpre hi, hch] at hP
  cases hP

/-- More actions of the same circuit make a longer pre-`θ` transcript. -/
theorem preThetaTranscriptForStatement_length_le_of_numProofs_le {shape shape' : Shape}
    (hc : shape.toCircuitShape = shape'.toCircuitShape) (hle : shape.numProofs ≤ shape'.numProofs)
    (vk vk' : F) (inst : Fin shape.numProofs → ℕ → G) (inst' : Fin shape'.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ps' : ProofString shape' F G) :
    (preThetaTranscriptForStatement vk inst ps).length
      ≤ (preThetaTranscriptForStatement vk' inst' ps').length := by
  have hcols : shape.numInstanceColumns = shape'.numInstanceColumns :=
    congrArg CircuitShape.numInstanceColumns hc
  have hadv : shape.numAdviceColumns = shape'.numAdviceColumns :=
    congrArg CircuitShape.numAdviceColumns hc
  rw [preThetaTranscriptForStatement_length, preThetaTranscriptForStatement_length, ← hcols,
    ← hadv]
  have h1 := Nat.mul_le_mul_right shape.numInstanceColumns hle
  have h2 := Nat.mul_le_mul_right shape.numAdviceColumns hle
  omega

/-- **The cones are disjoint.** No transcript extends the pre-`θ` prefixes of two different
action counts, so the two schedules never query the oracle at a common point. -/
theorem preTheta_cones_disjoint {shape shape' : Shape}
    (hc : shape.toCircuitShape = shape'.toCircuitShape)
    (hpos : 0 < shape.numInstanceColumns + shape.numAdviceColumns)
    (hne : shape.numProofs ≠ shape'.numProofs) (vk vk' : F)
    (inst : Fin shape.numProofs → ℕ → G) (inst' : Fin shape'.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ps' : ProofString shape' F G) (t : List (TranscriptElt F G)) :
    ¬ (preThetaTranscriptForStatement vk inst ps <+: t
        ∧ preThetaTranscriptForStatement vk' inst' ps' <+: t) := by
  rintro ⟨h1, h2⟩
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact preTheta_not_prefix_of_numProofs_lt hc hpos hlt vk vk' inst inst' ps ps'
      (List.prefix_of_prefix_length_le h1 h2
        (preThetaTranscriptForStatement_length_le_of_numProofs_le hc hlt.le vk vk' inst inst' ps ps'))
  · have hpos' : 0 < shape'.numInstanceColumns + shape'.numAdviceColumns := by
      rw [← congrArg CircuitShape.numInstanceColumns hc, ← congrArg CircuitShape.numAdviceColumns hc]
      exact hpos
    exact preTheta_not_prefix_of_numProofs_lt hc.symm hpos' hlt vk' vk inst' inst ps' ps
      (List.prefix_of_prefix_length_le h2 h1
        (preThetaTranscriptForStatement_length_le_of_numProofs_le hc.symm hlt.le vk' vk inst' inst
          ps' ps))

/-- **Prefix-freeness across action counts.** If two proof shapes have the same circuit but
different proof/action counts, neither statement-bound pre-`θ` transcript is a prefix of the
other. This is the explicit symmetric form of the separation used by the cone theorem. -/
theorem preTheta_prefixFree_of_numProofs_ne {shape shape' : Shape}
    (hc : shape.toCircuitShape = shape'.toCircuitShape)
    (hpos : 0 < shape.numInstanceColumns + shape.numAdviceColumns)
    (hne : shape.numProofs ≠ shape'.numProofs) (vk vk' : F)
    (inst : Fin shape.numProofs → ℕ → G) (inst' : Fin shape'.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ps' : ProofString shape' F G) :
    (¬ preThetaTranscriptForStatement vk inst ps <+:
        preThetaTranscriptForStatement vk' inst' ps') ∧
      (¬ preThetaTranscriptForStatement vk' inst' ps' <+:
        preThetaTranscriptForStatement vk inst ps) := by
  constructor
  · intro hprefix
    exact preTheta_cones_disjoint hc hpos hne vk vk' inst inst' ps ps' _
      ⟨hprefix, List.prefix_rfl⟩
  · intro hprefix
    exact preTheta_cones_disjoint hc hpos hne vk vk' inst inst' ps ps' _
      ⟨List.prefix_rfl, hprefix⟩

/-- **Byte-level disjointness.** No byte string extends the encoded pre-`θ` prefixes of two
different action counts: the deployed hash is never asked about a common prefix. -/
theorem encodeTranscript_cones_disjoint {shape shape' : Shape}
    (hc : shape.toCircuitShape = shape'.toCircuitShape)
    (hpos : 0 < shape.numInstanceColumns + shape.numAdviceColumns)
    (hne : shape.numProofs ≠ shape'.numProofs) (vk vk' : Fp)
    (inst : Fin shape.numProofs → ℕ → VestaG) (inst' : Fin shape'.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ps' : ProofString shape' Fp VestaG) (b : List UInt8) :
    ¬ (encodeTranscript (preThetaTranscriptForStatement vk inst ps) <+: b
        ∧ encodeTranscript (preThetaTranscriptForStatement vk' inst' ps') <+: b) := by
  rintro ⟨h1, h2⟩
  rcases le_total (encodeTranscript (preThetaTranscriptForStatement vk inst ps)).length
      (encodeTranscript (preThetaTranscriptForStatement vk' inst' ps')).length with hle | hle
  · have := encodeTranscript_prefix_iff.mp (List.prefix_of_prefix_length_le h1 h2 hle)
    exact preTheta_cones_disjoint hc hpos hne vk vk' inst inst' ps ps' _ ⟨this, List.prefix_rfl⟩
  · have := encodeTranscript_prefix_iff.mp (List.prefix_of_prefix_length_le h2 h1 hle)
    exact preTheta_cones_disjoint hc hpos hne vk vk' inst inst' ps ps' _ ⟨List.prefix_rfl, this⟩

/-- **Byte-level prefix-freeness across action counts.** The BLAKE2b input prefix for one action
count is never a prefix of the input prefix for another count, in either direction. -/
theorem encodeTranscript_prefixFree_of_numProofs_ne {shape shape' : Shape}
    (hc : shape.toCircuitShape = shape'.toCircuitShape)
    (hpos : 0 < shape.numInstanceColumns + shape.numAdviceColumns)
    (hne : shape.numProofs ≠ shape'.numProofs) (vk vk' : Fp)
    (inst : Fin shape.numProofs → ℕ → VestaG) (inst' : Fin shape'.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ps' : ProofString shape' Fp VestaG) :
    (¬ encodeTranscript (preThetaTranscriptForStatement vk inst ps) <+:
        encodeTranscript (preThetaTranscriptForStatement vk' inst' ps')) ∧
      (¬ encodeTranscript (preThetaTranscriptForStatement vk' inst' ps') <+:
        encodeTranscript (preThetaTranscriptForStatement vk inst ps)) := by
  constructor
  · intro hprefix
    exact (preTheta_prefixFree_of_numProofs_ne hc hpos hne vk vk' inst inst' ps ps').1
      (encodeTranscript_prefix_iff.mp hprefix)
  · intro hprefix
    exact (preTheta_prefixFree_of_numProofs_ne hc hpos hne vk vk' inst inst' ps ps').2
      (encodeTranscript_prefix_iff.mp hprefix)

open Classical in
/-- **Reprogramming the other count's cone is invisible.** Replacing the oracle's answers on every
transcript extending the `m`-action pre-`θ` prefix changes no `n`-action challenge, for `n ≠ m`:
the `n`-action schedule never queries there. -/
theorem deriveChallenges_reprogram_other_count [Zero F] {shape shape' : Shape}
    (hc : shape.toCircuitShape = shape'.toCircuitShape)
    (hpos : 0 < shape.numInstanceColumns + shape.numAdviceColumns)
    (hne : shape.numProofs ≠ shape'.numProofs) (fs : FiatShamir F G)
    (g : List (TranscriptElt F G) → F) (vk vk' : F)
    (inst : Fin shape.numProofs → ℕ → G) (inst' : Fin shape'.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ps' : ProofString shape' F G) :
    deriveChallenges
        ⟨fun t => if preThetaTranscriptForStatement vk' inst' ps' <+: t then g t else fs.squeeze t⟩
        (initialTranscript vk inst) ps
      = deriveChallenges fs (initialTranscript vk inst) ps := by
  apply deriveChallenges_congr_of_agree_on_cone
  intro t ht
  rw [← preThetaTranscriptForStatement_eq] at ht
  show (if preThetaTranscriptForStatement vk' inst' ps' <+: t then g t else fs.squeeze t)
    = fs.squeeze t
  rw [if_neg]
  intro ht'
  exact preTheta_cones_disjoint hc hpos hne vk vk' inst inst' ps ps' t ⟨ht, ht'⟩

end Zcash.Snark
