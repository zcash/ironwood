import Zcash.Snark.Soundness.Action.AdaptiveStatementTerminal
import Zcash.Snark.Soundness.AGM.AdaptiveIpaSurfaces

/-!
# Statistical surfaces for adaptive Action statements

An adaptive statement changes the verifier-controlled initial transcript from run to run.  The
bounded oracle domain still has one shape-determined length, so query-time decoders existentially
recover the canonical VK/instance prefix and ordinary proof represented by an annotated squeeze
point.  Equality of squeeze points pins that initial prefix, hence every configured public-instance
commitment, before any bad-set polynomial is reconstructed.
-/

namespace Zcash.Snark

open Classical CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open scoped ENNReal

local instance adaptiveStatementSurfacesVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

private theorem eq_of_prefixes_of_eq {A : Type*} {left right wholeLeft wholeRight : List A}
    (hleft : left <+: wholeLeft) (hright : right <+: wholeRight)
    (hwhole : wholeLeft = wholeRight) (hlen : left.length = right.length) :
    left = right := by
  rw [List.prefix_iff_eq_take] at hleft hright
  rw [hleft, hright, hwhole, hlen]

/-! ## Common fixed-length prefix wrappers -/

/-- The earlier pre-IPA prefix of a statement-bound query in the common adaptive domain. -/
def statementEarlierPrefix {pp : ProofParams}
    (t : AdaptiveActionStatementTranscript pp) (i : Fin 11) :
    AdaptiveActionStatementTranscript pp :=
  ⟨t.val.take (preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) i), by
    rw [List.length_take]
    exact le_trans (min_le_right _ _) t.prop⟩

/-- Truncating an actual selected-statement pre-IPA point recovers its earlier verifier point. -/
theorem statementEarlierPrefix_preIpaPoint {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11) (i : Fin (n : Nat)) :
    statementEarlierPrefix
        (family.preIpaPoint basis n (family.runOutput basis O))
        (i.castLE (le_of_lt n.isLt)) =
      family.preIpaPoint basis (i.castLE (le_of_lt n.isLt))
        (family.runOutput basis O) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (adaptiveEarlierPrefix_algebraicFullPrefixesPre
      ((family.runOutput basis O).init (family.vkTranscriptRepr basis))
      (family.runOutput basis O).toAlgebraicWfProof n i)
  simpa [statementEarlierPrefix, preIpaPoint,
    AdaptiveActionStatementOutput.prefixesPre,
    adaptiveEarlierPrefix, adaptiveStatementInitLength] using h

/-- At an exact index-`n` squeeze, every strict earlier prefix is a distinct oracle point. -/
theorem statementEarlierPrefix_ne {pp : ProofParams}
    (n : Fin 11) (t : AdaptiveActionStatementTranscript pp)
    (hlen : t.val.length = preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) n)
    (i : Fin (n : Nat)) :
    statementEarlierPrefix t (i.castLE (le_of_lt n.isLt)) ≠ t := by
  intro heq
  have hlens := congrArg (fun q : AdaptiveActionStatementTranscript pp => q.val.length) heq
  simp only [statementEarlierPrefix, List.length_take] at hlens
  have hlt : preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp))
      (i.castLE (le_of_lt n.isLt)) < t.val.length := by
    rw [hlen]
    exact preIpaLen_lt_at _ _ i.isLt
  rw [min_eq_left hlt.le] at hlens
  exact (Nat.ne_of_lt hlt) hlens

/-- A final-output bad set using only answers at strict earlier prefixes. -/
noncomputable def statementPrefixBad {pp : ProofParams} (n : Fin 11)
    (badF : AdaptiveActionStatementTranscript pp → (Fin (n : Nat) → Fp) → Set Fp)
    (t : AdaptiveActionStatementTranscript pp)
    (O : AdaptiveActionStatementTranscript pp → Fp) : Set Fp :=
  if t.val.length = preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) n then
    badF t (fun i => O (statementEarlierPrefix t
      (i.castLE (le_of_lt n.isLt))))
  else ∅

/-- A query-label bad set using only the pre-answer annotation and strict earlier answers. -/
noncomputable def statementLabeledPrefixBad {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11)
    (badF : (t : AdaptiveActionStatementTranscript pp) →
      AlgebraicTranscriptQuery (F := Fp) basis t →
      (Fin (n : Nat) → Fp) → Set Fp)
    (t : AdaptiveActionStatementTranscript pp)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : AdaptiveActionStatementTranscript pp → Fp) : Set Fp :=
  if t.val.length = preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) n then
    badF t label (fun i => O (statementEarlierPrefix t
      (i.castLE (le_of_lt n.isLt))))
  else ∅

theorem statementPrefixBad_update_self {pp : ProofParams} (n : Fin 11)
    (badF : AdaptiveActionStatementTranscript pp → (Fin (n : Nat) → Fp) → Set Fp)
    (t : AdaptiveActionStatementTranscript pp)
    (O : AdaptiveActionStatementTranscript pp → Fp) (v : Fp) :
    statementPrefixBad n badF t (Function.update O t v) =
      statementPrefixBad n badF t O := by
  unfold statementPrefixBad
  split
  · rename_i hlen
    congr 1
    funext i
    rw [Function.update_of_ne]
    exact statementEarlierPrefix_ne n t hlen i
  · rfl

theorem statementLabeledPrefixBad_update_self {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11)
    (badF : (t : AdaptiveActionStatementTranscript pp) →
      AlgebraicTranscriptQuery (F := Fp) basis t →
      (Fin (n : Nat) → Fp) → Set Fp)
    (t : AdaptiveActionStatementTranscript pp)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : AdaptiveActionStatementTranscript pp → Fp) (v : Fp) :
    statementLabeledPrefixBad basis n badF t label (Function.update O t v) =
      statementLabeledPrefixBad basis n badF t label O := by
  unfold statementLabeledPrefixBad
  split
  · rename_i hlen
    congr 1
    funext i
    rw [Function.update_of_ne]
    exact statementEarlierPrefix_ne n t hlen i
  · rfl

theorem statementPrefixBad_measure_le {pp : ProofParams} (n : Fin 11)
    (badF : AdaptiveActionStatementTranscript pp → (Fin (n : Nat) → Fp) → Set Fp)
    {epsilon : ENNReal}
    (hbad : ∀ t earlier,
      uniformChallenge.toOuterMeasure (badF t earlier) ≤ epsilon)
    (t : AdaptiveActionStatementTranscript pp)
    (O : AdaptiveActionStatementTranscript pp → Fp) :
    uniformChallenge.toOuterMeasure (statementPrefixBad n badF t O) ≤ epsilon := by
  unfold statementPrefixBad
  split
  · exact hbad _ _
  · simp

theorem statementLabeledPrefixBad_measure_le {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11)
    (badF : (t : AdaptiveActionStatementTranscript pp) →
      AlgebraicTranscriptQuery (F := Fp) basis t →
      (Fin (n : Nat) → Fp) → Set Fp)
    {epsilon : ENNReal}
    (hbad : ∀ t label earlier,
      uniformChallenge.toOuterMeasure (badF t label earlier) ≤ epsilon)
    (t : AdaptiveActionStatementTranscript pp)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : AdaptiveActionStatementTranscript pp → Fp) :
    uniformChallenge.toOuterMeasure
        (statementLabeledPrefixBad basis n badF t label O) ≤ epsilon := by
  unfold statementLabeledPrefixBad
  split
  · exact hbad _ _ _
  · simp

/-- A canonical statement-bound pre-IPA squeeze embedded in the common adaptive oracle domain. -/
def prefixesPreOf {pp : ProofParams}
    (vkTranscriptRepr : Fp)
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG)
    (proof : WfProof (AdaptiveActionStatementShape pp))
    (n : Fin 11) : AdaptiveActionStatementTranscript pp :=
  let t := fullPrefixesPre (initialTranscript vkTranscriptRepr instanceCommitment) proof n
  ⟨t.val, by simpa [adaptiveStatementInitLength] using t.prop⟩

/-- A canonical statement-bound IPA squeeze embedded in the same common oracle domain. -/
def prefixesOf {pp : ProofParams}
    (vkTranscriptRepr : Fp)
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG)
    (proof : WfProof (AdaptiveActionStatementShape pp))
    (j : Fin (AdaptiveActionStatementShape pp).k) : AdaptiveActionStatementTranscript pp :=
  let t := fullPrefixes (initialTranscript vkTranscriptRepr instanceCommitment) proof j
  ⟨t.val, by simpa [adaptiveStatementInitLength] using t.prop⟩

@[simp] theorem prefixesPreOf_output {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (n : Fin 11) :
    prefixesPreOf vkTranscriptRepr
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        output.toAlgebraicWfProof.proof n =
      output.prefixesPre vkTranscriptRepr n := by
  rfl

@[simp] theorem prefixesOf_output {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (j : Fin (AdaptiveActionStatementShape pp).k) :
    prefixesOf vkTranscriptRepr
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        output.toAlgebraicWfProof.proof j =
      output.prefixes vkTranscriptRepr j := by
  rfl

/-- A canonical verifier prefix and well-formed proof decoded from one pre-IPA query point. -/
structure DecodedStatementPrePrefix (pp : ProofParams) (n : Fin 11)
    (t : AdaptiveActionStatementTranscript pp) where
  vkTranscriptRepr : Fp
  instanceCommitment :
    Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG
  proof : WfProof (AdaptiveActionStatementShape pp)
  point_eq : prefixesPreOf vkTranscriptRepr instanceCommitment proof n = t

/-- A canonical verifier prefix and well-formed proof decoded from one IPA query point. -/
structure DecodedStatementIpaPrefix (pp : ProofParams)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (t : AdaptiveActionStatementTranscript pp) where
  vkTranscriptRepr : Fp
  instanceCommitment :
    Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG
  proof : WfProof (AdaptiveActionStatementShape pp)
  point_eq : prefixesOf vkTranscriptRepr instanceCommitment proof j = t

/-- Choose a valid pre-IPA decode, or `none`. This noncomputable choice only defines a probability
surface; relation extraction is census-pinned as executable. -/
noncomputable def decodeStatementPrePrefix? {pp : ProofParams} (n : Fin 11)
    (t : AdaptiveActionStatementTranscript pp) :
    Option (DecodedStatementPrePrefix pp n t) :=
  if h : Nonempty (DecodedStatementPrePrefix pp n t) then some (Classical.choice h) else none

/-- Choose a valid IPA-prefix decode, or `none`. This noncomputable choice only defines a
probability surface; relation extraction remains executable. -/
noncomputable def decodeStatementIpaPrefix? {pp : ProofParams}
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (t : AdaptiveActionStatementTranscript pp) :
    Option (DecodedStatementIpaPrefix pp j t) :=
  if h : Nonempty (DecodedStatementIpaPrefix pp j t) then some (Classical.choice h) else none

/-- Every actual output-selected pre-IPA squeeze has a canonical decode. -/
theorem decodeStatementPrePrefix?_isSome {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11) :
    (decodeStatementPrePrefix? n (family.preIpaPoint basis n
      (family.runOutput basis O))).isSome := by
  have h : Nonempty (DecodedStatementPrePrefix pp n
      (family.preIpaPoint basis n (family.runOutput basis O))) := ⟨
    { vkTranscriptRepr := family.vkTranscriptRepr basis
      instanceCommitment := adaptiveActionStatementInstanceCommitment pp basis
        (family.runOutput basis O).inputs
      proof := (family.runOutput basis O).toAlgebraicWfProof.proof
      point_eq := by rfl }⟩
  rw [decodeStatementPrePrefix?, dif_pos h]
  rfl

/-- Every actual output-selected IPA squeeze has a canonical decode. -/
theorem decodeStatementIpaPrefix?_isSome {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k) :
    (decodeStatementIpaPrefix? j (family.ipaPoint basis j
      (family.runOutput basis O))).isSome := by
  have h : Nonempty (DecodedStatementIpaPrefix pp j
      (family.ipaPoint basis j (family.runOutput basis O))) := ⟨
    { vkTranscriptRepr := family.vkTranscriptRepr basis
      instanceCommitment := adaptiveActionStatementInstanceCommitment pp basis
        (family.runOutput basis O).inputs
      proof := (family.runOutput basis O).toAlgebraicWfProof.proof
      point_eq := by rfl }⟩
  rw [decodeStatementIpaPrefix?, dif_pos h]
  rfl

/-- Equal adaptive pre-IPA query points pin the complete canonical verifier prefix. -/
theorem DecodedStatementPrePrefix.initialTranscript_eq_output {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11)
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp n t)
    (ht : t = family.preIpaPoint basis n (family.runOutput basis O)) :
    initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment =
      (family.runOutput basis O).init (family.vkTranscriptRepr basis) := by
  let output := family.runOutput basis O
  have hpoint : preIpaSqueezePoints
        (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
        decoded.proof.1 n =
      preIpaSqueezePoints (output.init (family.vkTranscriptRepr basis))
        output.toAlgebraicWfProof.proof.1 n := by
    exact congrArg Subtype.val (decoded.point_eq.trans (ht.trans (by rfl)))
  apply initial_eq_of_preIpaSqueezePoints_eq _ _ _ _ n
  · simp [adaptiveStatementInitLength]
  · exact hpoint

/-- Consequently every configured instance-commitment point decoded at that query is the point
derived from the adversary-selected public statement. -/
theorem DecodedStatementPrePrefix.instanceCommitment_eq_output {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11)
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp n t)
    (ht : t = family.preIpaPoint basis n (family.runOutput basis O))
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns) :
    decoded.instanceCommitment p column =
      adaptiveActionStatementInstanceCommitment pp basis
        (family.runOutput basis O).inputs p column := by
  exact instanceCommitment_eq_of_initialTranscript_eq _ _ _ _
    (decoded.initialTranscript_eq_output family basis O n ht) p column

/-- Bounded totalization turns configured-column equality into equality of the complete verifier
function used by query-local surfaces. -/
theorem DecodedStatementPrePrefix.boundedInstanceCommitment_eq_output {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11)
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp n t)
    (ht : t = family.preIpaPoint basis n (family.runOutput basis O)) :
    boundedAdaptiveStatementInstanceCommitment pp basis decoded.instanceCommitment =
      adaptiveActionStatementInstanceCommitment pp basis
        (family.runOutput basis O).inputs := by
  rw [adaptiveActionStatementInstanceCommitment_eq_bounded]
  funext p column
  unfold boundedAdaptiveStatementInstanceCommitment
  by_cases hcolumn : column < (AdaptiveActionStatementShape pp).numInstanceColumns
  · rw [if_pos hcolumn, if_pos hcolumn]
    exact decoded.instanceCommitment_eq_output family basis O n ht p ⟨column, hcolumn⟩
  · rw [if_neg hcolumn, if_neg hcolumn]

/-- Equal adaptive IPA query points likewise pin the canonical verifier prefix. -/
theorem DecodedStatementIpaPrefix.initialTranscript_eq_output {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k)
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementIpaPrefix pp j t)
    (ht : t = family.ipaPoint basis j (family.runOutput basis O)) :
    initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment =
      (family.runOutput basis O).init (family.vkTranscriptRepr basis) := by
  subst t
  let output := family.runOutput basis O
  let decodedInit := initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment
  let outputInit := output.init (family.vkTranscriptRepr basis)
  have hpoint := congrArg Subtype.val decoded.point_eq
  change roundTranscriptFin
        (preIpaTranscript decodedInit decoded.proof.1) decoded.proof.1.ipaRounds j =
      roundTranscriptFin (preIpaTranscript outputInit
        output.toAlgebraicWfProof.proof.1)
        output.toAlgebraicWfProof.proof.1.ipaRounds j at hpoint
  have hleft : decodedInit <+: roundTranscriptFin
      (preIpaTranscript decodedInit decoded.proof.1) decoded.proof.1.ipaRounds j :=
    (initial_prefix_preIpaSqueezePoints decodedInit decoded.proof.1 0).trans
      ((preIpaSqueezePoints_prefix decodedInit decoded.proof.1 0).trans (by
        unfold roundTranscriptFin
        exact List.prefix_append _ _))
  have hright : outputInit <+: roundTranscriptFin
      (preIpaTranscript outputInit output.toAlgebraicWfProof.proof.1)
      output.toAlgebraicWfProof.proof.1.ipaRounds j :=
    (initial_prefix_preIpaSqueezePoints outputInit output.toAlgebraicWfProof.proof.1 0).trans
      ((preIpaSqueezePoints_prefix outputInit output.toAlgebraicWfProof.proof.1 0).trans (by
        unfold roundTranscriptFin
        exact List.prefix_append _ _))
  apply eq_of_prefixes_of_eq hleft hright hpoint
  simp [decodedInit, outputInit, adaptiveStatementInitLength]

/-- Every configured instance point decoded at an IPA query is therefore the selected
statement's actual public-instance commitment. -/
theorem DecodedStatementIpaPrefix.instanceCommitment_eq_output {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k)
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementIpaPrefix pp j t)
    (ht : t = family.ipaPoint basis j (family.runOutput basis O))
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns) :
    decoded.instanceCommitment p column =
      adaptiveActionStatementInstanceCommitment pp basis
        (family.runOutput basis O).inputs p column := by
  exact instanceCommitment_eq_of_initialTranscript_eq _ _ _ _
    (decoded.initialTranscript_eq_output family basis O j ht) p column

/-- IPA-prefix counterpart of `boundedInstanceCommitment_eq_output`. -/
theorem DecodedStatementIpaPrefix.boundedInstanceCommitment_eq_output {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k)
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementIpaPrefix pp j t)
    (ht : t = family.ipaPoint basis j (family.runOutput basis O)) :
    boundedAdaptiveStatementInstanceCommitment pp basis decoded.instanceCommitment =
      adaptiveActionStatementInstanceCommitment pp basis
        (family.runOutput basis O).inputs := by
  rw [adaptiveActionStatementInstanceCommitment_eq_bounded]
  funext p column
  unfold boundedAdaptiveStatementInstanceCommitment
  by_cases hcolumn : column < (AdaptiveActionStatementShape pp).numInstanceColumns
  · rw [if_pos hcolumn, if_pos hcolumn]
    exact decoded.instanceCommitment_eq_output family basis O j ht p ⟨column, hcolumn⟩
  · rw [if_neg hcolumn, if_neg hcolumn]

/-! ## Query-local coordinate sources -/

/-- Configured instance-commitment points in deployed proof-major, column-major order. -/
def statementInstancePoints {pp : ProofParams}
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG) : List VestaG :=
  (List.ofFn fun p => List.ofFn fun column :
    Fin (AdaptiveActionStatementShape pp).numInstanceColumns =>
      instanceCommitment p column).flatten

/-- Points whose coordinates affect one multiopen/root squeeze. -/
def DecodedStatementPrePrefix.rootPoints {pp : ProofParams} {n : Fin 11}
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp n t) : List VestaG :=
  decoded.proof.1.commitmentPointsBefore n ++
    statementInstancePoints decoded.instanceCommitment

/-- Every decoded root-source point occurs in the exact annotated query transcript. -/
theorem DecodedStatementPrePrefix.rootPoints_covered {pp : ProofParams}
    {n : Fin 11} (h5n : 5 ≤ (n : Nat))
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp n t) :
    ∀ P ∈ decoded.rootPoints,
      P ∈ transcriptGroupPoints t.val := by
  intro P hP
  rw [DecodedStatementPrePrefix.rootPoints, List.mem_append] at hP
  rw [← decoded.point_eq]
  rcases hP with hproof | hinstance
  · exact decoded.proof.1.commitmentPointsBefore_covered
      (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
      decoded.proof.2 n h5n P hproof
  · rw [statementInstancePoints] at hinstance
    obtain ⟨row, hrow, hcolumn⟩ := List.mem_flatten.mp hinstance
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hrow
    obtain ⟨column, hc⟩ := List.mem_ofFn.mp (hp ▸ hcolumn)
    rw [← hc]
    apply mem_transcriptGroupPoints_of_mem_point
    apply (initial_prefix_preIpaSqueezePoints
      (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
      decoded.proof.1 n).mem
    exact instanceCommitment_mem_initialTranscript decoded.vkTranscriptRepr
      decoded.instanceCommitment p column

/-- Query-time root source reconstructed solely from the ordinary prefix and its pre-answer AGM
annotation, followed by verifier-fixed key representations. -/
def decodedRootQuerySource {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    {n : Fin 11} (h5n : 5 ≤ (n : Nat))
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp n t)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) :
    List (AlgebraicPoint (F := Fp) basis) :=
  label.representationsForPoints decoded.rootPoints
    (decoded.rootPoints_covered h5n) ++
      family.fixedRepresentations basis

/-- Erasing final root-target coordinates gives the ordinary proof points followed by the
selected public-instance commitments. -/
theorem preIpaRepresentationTarget_points {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (n : Fin 11) :
    (preIpaRepresentationTarget output n).map AlgebraicPoint.point =
      output.toAlgebraicWfProof.proof.1.commitmentPointsBefore n ++
        statementInstancePoints
          (adaptiveActionStatementInstanceCommitment pp basis output.inputs) := by
  rw [preIpaRepresentationTarget, List.map_append,
    output.proofData.algebraicProof.representationsBefore_points]
  congr 1
  unfold adaptiveStatementInstanceRepresentationList statementInstancePoints
  simp only [List.map_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  simp only [Function.comp_apply, List.map_ofFn]
  apply congrArg List.ofFn
  funext column
  exact output.instanceRepresented p column

/-- Outside the phase-local relation branch, a first annotated root query reconstructs exactly
the final output's root source. -/
theorem decodedRootQuerySource_eq_of_pinned {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11) (h5n : 5 ≤ (n : Nat))
    (decoded : DecodedStatementPrePrefix pp n
      (family.preIpaPoint basis n (family.runOutput basis O)))
    (pinned : SelectedQueryRepresentationPinned
      (family.preIpaPoint basis n (family.runOutput basis O))
      (family.adversary basis) O
      (preIpaRepresentationTarget (family.runOutput basis O) n)) :
    decodedRootQuerySource family basis h5n decoded pinned.query =
      preIpaRepresentationTarget (family.runOutput basis O) n ++
        family.fixedRepresentations basis := by
  let output := family.runOutput basis O
  let final := preIpaRepresentationTarget output n
  have hinit := decoded.initialTranscript_eq_output family basis O n rfl
  have hprefix : preIpaSqueezePoints
        (output.init (family.vkTranscriptRepr basis)) decoded.proof.1 n =
      preIpaSqueezePoints (output.init (family.vkTranscriptRepr basis))
        output.toAlgebraicWfProof.proof.1 n := by
    have h := congrArg Subtype.val decoded.point_eq
    change (preIpaSqueezePoints
        (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
        decoded.proof.1 n) = _ at h
    rw [hinit] at h
    exact h
  have hcanonical := adaptiveRootPrefixProof_congr
    (output.init (family.vkTranscriptRepr basis)) n h5n
    decoded.proof.1 output.toAlgebraicWfProof.proof.1
    decoded.proof.2 output.toAlgebraicWfProof.proof.2 hprefix
  have hordinary : decoded.proof.1.commitmentPointsBefore n =
      output.toAlgebraicWfProof.proof.1.commitmentPointsBefore n := by
    calc
      decoded.proof.1.commitmentPointsBefore n =
          (adaptiveRootPrefixProof n decoded.proof.1).commitmentPointsBefore n := by simp
      _ = (adaptiveRootPrefixProof n output.toAlgebraicWfProof.proof.1).commitmentPointsBefore n :=
        congrArg (fun ps => ps.commitmentPointsBefore n) hcanonical
      _ = output.toAlgebraicWfProof.proof.1.commitmentPointsBefore n := by simp
  have hinstances : statementInstancePoints decoded.instanceCommitment =
      statementInstancePoints
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs) := by
    unfold statementInstancePoints
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext p
    apply congrArg List.ofFn
    funext column
    exact decoded.instanceCommitment_eq_output family basis O n rfl p column
  have hpoints : decoded.rootPoints = final.map AlgebraicPoint.point := by
    rw [DecodedStatementPrePrefix.rootPoints, hordinary, hinstances,
      preIpaRepresentationTarget_points]
  have hselected : pinned.query.representationsFor final pinned.covered = final :=
    algebraicPointList_eq_of_maps_eq
      (pinned.query.representationsFor_points final pinned.covered)
      pinned.coefficients_eq
  let decodedCovered := decoded.rootPoints_covered h5n
  let finalCoveredPoints : ∀ P ∈ final.map AlgebraicPoint.point,
      P ∈ transcriptGroupPoints
        (family.preIpaPoint basis n output).val := by
    intro P hP
    obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hP
    exact pinned.covered ap hap
  have hqueryPoints : pinned.query.representationsForPoints
      decoded.rootPoints decodedCovered =
      pinned.query.representationsForPoints
        (final.map AlgebraicPoint.point) finalCoveredPoints := by
    exact pinned.query.representationsForPoints_congr _ _
      decodedCovered finalCoveredPoints hpoints
  unfold decodedRootQuerySource
  rw [hqueryPoints,
    ← pinned.query.representationsFor_eq_representationsForPoints final pinned.covered,
    hselected]

/-! ## IPA-round coordinate sources -/

/-- Points whose coordinates affect the IPA quadratic at round `j`, including the public
instance commitments already absorbed in the canonical initial transcript. -/
def DecodedStatementIpaPrefix.ipaPoints {pp : ProofParams}
    {j : Fin (AdaptiveActionStatementShape pp).k}
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementIpaPrefix pp j t) : List VestaG :=
  decoded.proof.1.commitmentPointsBeforeRound j ++
    statementInstancePoints decoded.instanceCommitment

/-- Every decoded IPA source point occurs in the exact annotated round query. -/
theorem DecodedStatementIpaPrefix.ipaPoints_covered {pp : ProofParams}
    {j : Fin (AdaptiveActionStatementShape pp).k}
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementIpaPrefix pp j t) :
    ∀ P ∈ decoded.ipaPoints, P ∈ transcriptGroupPoints t.val := by
  intro P hP
  rw [DecodedStatementIpaPrefix.ipaPoints, List.mem_append] at hP
  rw [← decoded.point_eq]
  rcases hP with hproof | hinstance
  · exact decoded.proof.1.commitmentPointsBeforeRound_covered
      (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
      decoded.proof.2 j P hproof
  · rw [statementInstancePoints] at hinstance
    obtain ⟨row, hrow, hcolumn⟩ := List.mem_flatten.mp hinstance
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hrow
    obtain ⟨column, hc⟩ := List.mem_ofFn.mp (hp ▸ hcolumn)
    rw [← hc]
    apply mem_transcriptGroupPoints_of_mem_point
    have hinit : initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment <+:
        roundTranscriptFin
          (preIpaTranscript
            (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
            decoded.proof.1)
          decoded.proof.1.ipaRounds j :=
      (initial_prefix_preIpaSqueezePoints
        (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
        decoded.proof.1 0).trans
        ((preIpaSqueezePoints_prefix
          (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
          decoded.proof.1 0).trans (by
            unfold roundTranscriptFin
            exact List.prefix_append _ _))
    exact hinit.mem (instanceCommitment_mem_initialTranscript decoded.vkTranscriptRepr
      decoded.instanceCommitment p column)

/-- Recover one query-time coordinate of a decoded adaptive-statement IPA prefix. -/
def decodedIpaQueryRepresentation {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    {j : Fin (AdaptiveActionStatementShape pp).k}
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementIpaPrefix pp j t)
    (query : AlgebraicTranscriptQuery (F := Fp) basis t)
    (P : VestaG) (hP : P ∈ decoded.ipaPoints) :
    AlgebraicPoint (F := Fp) basis :=
  query.representationOfPoint P (decoded.ipaPoints_covered P hP)

/-- Explicit coordinates fixed by the first annotation of one adaptive-statement IPA query. -/
def decodedIpaQueryCoordinates {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    {j : Fin (AdaptiveActionStatementShape pp).k}
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementIpaPrefix pp j t)
    (query : AlgebraicTranscriptQuery (F := Fp) basis t) :
    AdaptiveIpaCoordinateData basis where
  multiopenSource :=
    query.representationsForPoints decoded.proof.1.preX1CommitmentPoints (by
      intro P hP
      exact decoded.ipaPoints_covered P (by
        apply List.mem_append_left
        exact decoded.proof.1.preX1CommitmentPoints_mem_beforeRound j P hP)) ++
      query.representationsForPoints
        (statementInstancePoints decoded.instanceCommitment) (by
          intro P hP
          exact decoded.ipaPoints_covered P (List.mem_append_right _ hP)) ++
      family.fixedRepresentations basis ++
      [decodedIpaQueryRepresentation basis decoded query decoded.proof.1.multiopenQPrime
        (List.mem_append_left _ (decoded.proof.1.multiopenQPrime_mem_beforeRound j))]
  s := decodedIpaQueryRepresentation basis decoded query decoded.proof.1.ipaS
    (List.mem_append_left _ (decoded.proof.1.ipaS_mem_beforeRound j))
  rounds := fun i =>
    if hij : i.val ≤ j.val then
      (decodedIpaQueryRepresentation basis decoded query (decoded.proof.1.ipaRounds i).1
          (List.mem_append_left _ (decoded.proof.1.ipaRound_mem_beforeRound j i hij).1),
        decodedIpaQueryRepresentation basis decoded query (decoded.proof.1.ipaRounds i).2
          (List.mem_append_left _ (decoded.proof.1.ipaRound_mem_beforeRound j i hij).2))
    else (adaptiveZeroAlgebraicPoint basis, adaptiveZeroAlgebraicPoint basis)

/-- Erasing the final IPA annotation target gives the ordinary round-prefix points followed by
the selected public-instance commitments. -/
theorem ipaRepresentationTarget_points {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (j : Fin (AdaptiveActionStatementShape pp).k) :
    (ipaRepresentationTarget output j).map AlgebraicPoint.point =
      output.toAlgebraicWfProof.proof.1.commitmentPointsBeforeRound j ++
        statementInstancePoints
          (adaptiveActionStatementInstanceCommitment pp basis output.inputs) := by
  rw [ipaRepresentationTarget, List.map_append,
    output.proofData.algebraicProof.representationsBeforeRound_points]
  congr 1
  unfold adaptiveStatementInstanceRepresentationList statementInstancePoints
  simp only [List.map_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  simp only [Function.comp_apply, List.map_ofFn]
  apply congrArg List.ofFn
  funext column
  exact output.instanceRepresented p column

/-- If the IPA provenance finder returned no relation, coordinates decoded from the first actual
round annotation are exactly the final coordinates visible through that query. -/
theorem decodedIpaQueryCoordinates_eq_of_pinned {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k)
    (decoded : DecodedStatementIpaPrefix pp j
      (family.ipaPoint basis j (family.runOutput basis O)))
    (pinned : SelectedQueryRepresentationPinned
      (family.ipaPoint basis j (family.runOutput basis O))
      (family.adversary basis) O
      (ipaRepresentationTarget (family.runOutput basis O) j)) :
    decodedIpaQueryCoordinates family basis decoded pinned.query =
      ((family.runOutput basis O).proofData.adaptiveIpaCoordinates.prefix basis j) := by
  let output := family.runOutput basis O
  let final := ipaRepresentationTarget output j
  let outputInit := output.init (family.vkTranscriptRepr basis)
  have hinit := decoded.initialTranscript_eq_output family basis O j rfl
  have hpoint : fullPrefixes outputInit decoded.proof j =
      fullPrefixes outputInit output.toAlgebraicWfProof.proof j := by
    apply Subtype.ext
    have h := congrArg Subtype.val decoded.point_eq
    change (fullPrefixes
        (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
        decoded.proof j).val =
      (fullPrefixes outputInit output.toAlgebraicWfProof.proof j).val at h
    rw [hinit] at h
    exact h
  have hpre := preIpaTranscript_eq_of_fullPrefix_eq outputInit decoded.proof
    output.toAlgebraicWfProof.proof j hpoint
  have hsplice : decoded.proof.1 = spliceIpa output.proofData.algebraicProof.erase
      decoded.proof.1.ipaRounds decoded.proof.1.ipaC decoded.proof.1.ipaF :=
    preIpaTranscript_inj outputInit decoded.proof.2 output.proofData.wellFormed hpre
  have hselected : pinned.query.representationsFor final pinned.covered = final :=
    algebraicPointList_eq_of_maps_eq
      (pinned.query.representationsFor_points final pinned.covered)
      pinned.coefficients_eq
  have hpreSubset : ∀ ap ∈ output.proofData.algebraicProof.preX1Points, ap ∈ final := by
    intro ap hap
    apply List.mem_append_left
    apply List.mem_append_left
    exact output.proofData.algebraicProof.preX1Points_mem_representationsBefore 10 ap hap
  have hinstanceSubset : ∀ ap ∈
      adaptiveStatementInstanceRepresentationList output.instanceRepresentations,
      ap ∈ final := by
    intro ap hap
    apply List.mem_append_right
    exact hap
  have hqSubset : output.proofData.algebraicProof.multiopenQPrime ∈ final := by
    apply List.mem_append_left
    apply List.mem_append_left
    exact output.proofData.algebraicProof.multiopenQPrime_mem_representationsBefore 10 (by omega)
  have hsSubset : output.proofData.algebraicProof.ipaS ∈ final := by
    apply List.mem_append_left
    apply List.mem_append_left
    exact output.proofData.algebraicProof.ipaS_mem_representationsBefore 10 (by omega)
  have hprePoints : decoded.proof.1.preX1CommitmentPoints =
      output.proofData.algebraicProof.preX1Points.map AlgebraicPoint.point := by
    calc
      decoded.proof.1.preX1CommitmentPoints =
          output.proofData.algebraicProof.erase.preX1CommitmentPoints := by
            rw [hsplice]
            rfl
      _ = output.proofData.algebraicProof.preX1Points.map AlgebraicPoint.point := by
        have hp := output.proofData.algebraicProof.representationsBefore_points (5 : Fin 11)
        simpa [AlgebraicProofString.representationsBefore,
          ProofString.commitmentPointsBefore] using hp.symm
  have hinstancePoints : statementInstancePoints decoded.instanceCommitment =
      (adaptiveStatementInstanceRepresentationList output.instanceRepresentations).map
        AlgebraicPoint.point := by
    unfold statementInstancePoints adaptiveStatementInstanceRepresentationList
    simp only [List.map_flatten, List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext p
    simp only [Function.comp_apply, List.map_ofFn]
    apply congrArg List.ofFn
    funext column
    simp only [Function.comp_apply]
    rw [output.instanceRepresented]
    exact decoded.instanceCommitment_eq_output family basis O j rfl p column
  have hpreSelected : pinned.query.representationsForPoints
      decoded.proof.1.preX1CommitmentPoints (by
        intro P hP
        exact decoded.ipaPoints_covered P (by
          apply List.mem_append_left
          exact decoded.proof.1.preX1CommitmentPoints_mem_beforeRound j P hP)) =
      output.proofData.algebraicProof.preX1Points := by
    let decodedCovered : ∀ P ∈ decoded.proof.1.preX1CommitmentPoints,
        P ∈ transcriptGroupPoints (family.ipaPoint basis j output).val := by
      intro P hP
      exact decoded.ipaPoints_covered P (by
        apply List.mem_append_left
        exact decoded.proof.1.preX1CommitmentPoints_mem_beforeRound j P hP)
    let finalCovered : ∀ P ∈
        output.proofData.algebraicProof.preX1Points.map AlgebraicPoint.point,
        P ∈ transcriptGroupPoints (family.ipaPoint basis j output).val := by
      intro P hP
      obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hP
      exact pinned.covered ap (hpreSubset ap hap)
    have hqueryPoints := pinned.query.representationsForPoints_congr
      decoded.proof.1.preX1CommitmentPoints
      (output.proofData.algebraicProof.preX1Points.map AlgebraicPoint.point)
      decodedCovered finalCovered hprePoints
    rw [hqueryPoints,
      ← pinned.query.representationsFor_eq_representationsForPoints
        output.proofData.algebraicProof.preX1Points]
    exact pinned.representationsFor_eq_self_of_subset hpreSubset
  have hinstanceSelected : pinned.query.representationsForPoints
      (statementInstancePoints decoded.instanceCommitment) (by
        intro P hP
        exact decoded.ipaPoints_covered P (List.mem_append_right _ hP)) =
      adaptiveStatementInstanceRepresentationList output.instanceRepresentations := by
    let decodedCovered : ∀ P ∈ statementInstancePoints decoded.instanceCommitment,
        P ∈ transcriptGroupPoints (family.ipaPoint basis j output).val := by
      intro P hP
      exact decoded.ipaPoints_covered P (List.mem_append_right _ hP)
    let finalCovered : ∀ P ∈
        (adaptiveStatementInstanceRepresentationList output.instanceRepresentations).map
          AlgebraicPoint.point,
        P ∈ transcriptGroupPoints (family.ipaPoint basis j output).val := by
      intro P hP
      obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hP
      exact pinned.covered ap (hinstanceSubset ap hap)
    have hqueryPoints := pinned.query.representationsForPoints_congr
      (statementInstancePoints decoded.instanceCommitment)
      ((adaptiveStatementInstanceRepresentationList output.instanceRepresentations).map
        AlgebraicPoint.point) decodedCovered finalCovered hinstancePoints
    rw [hqueryPoints,
      ← pinned.query.representationsFor_eq_representationsForPoints
        (adaptiveStatementInstanceRepresentationList output.instanceRepresentations)]
    exact pinned.representationsFor_eq_self_of_subset hinstanceSubset
  have hqPoint : decoded.proof.1.multiopenQPrime =
      output.proofData.algebraicProof.multiopenQPrime.point := by
    rw [hsplice]
    rfl
  have hsPoint : decoded.proof.1.ipaS =
      output.proofData.algebraicProof.ipaS.point := by
    rw [hsplice]
    rfl
  have hqSelected : decodedIpaQueryRepresentation basis decoded pinned.query
      decoded.proof.1.multiopenQPrime
        (List.mem_append_left _ (decoded.proof.1.multiopenQPrime_mem_beforeRound j)) =
      output.proofData.algebraicProof.multiopenQPrime := by
    unfold decodedIpaQueryRepresentation
    have htarget := pinned.query.representationOfPoint_eq_of_representationsFor_eq
      final pinned.covered hselected output.proofData.algebraicProof.multiopenQPrime hqSubset
    exact (pinned.query.representationOfPoint_congr _ _ _ _ hqPoint).trans htarget
  have hsSelected : decodedIpaQueryRepresentation basis decoded pinned.query
      decoded.proof.1.ipaS
        (List.mem_append_left _ (decoded.proof.1.ipaS_mem_beforeRound j)) =
      output.proofData.algebraicProof.ipaS := by
    unfold decodedIpaQueryRepresentation
    have htarget := pinned.query.representationOfPoint_eq_of_representationsFor_eq
      final pinned.covered hselected output.proofData.algebraicProof.ipaS hsSubset
    exact (pinned.query.representationOfPoint_congr _ _ _ _ hsPoint).trans htarget
  apply AdaptiveIpaCoordinateData.ext'
  · change pinned.query.representationsForPoints
        decoded.proof.1.preX1CommitmentPoints _ ++
        pinned.query.representationsForPoints
          (statementInstancePoints decoded.instanceCommitment) _ ++
        family.fixedRepresentations basis ++
        [decodedIpaQueryRepresentation basis decoded pinned.query
          decoded.proof.1.multiopenQPrime _] = _
    rw [hpreSelected, hinstanceSelected, hqSelected]
    change output.proofData.algebraicProof.preX1Points ++
        adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
          family.fixedRepresentations basis ++
            [output.proofData.algebraicProof.multiopenQPrime] =
      (output.proofData.adaptiveIpaCoordinates.prefix basis j).multiopenSource
    simp [OnlineMemberProofData.adaptiveIpaCoordinates, AdaptiveIpaCoordinateData.prefix,
      AlgebraicProofString.multiopenAssemblySource,
      AlgebraicProofString.preX1AssemblySource, List.append_assoc]
  · exact hsSelected
  · funext i
    by_cases hij : i.val ≤ j.val
    · have hroundPoint := ipaRound_eq_of_fullPrefix_eq outputInit decoded.proof
        output.toAlgebraicWfProof.proof j i hij hpoint
      have hroundSubset :=
        output.proofData.algebraicProof.ipaRound_mem_representationsBeforeRound j i hij
      have hL : decodedIpaQueryRepresentation basis decoded pinned.query
          (decoded.proof.1.ipaRounds i).1
            (List.mem_append_left _
              (decoded.proof.1.ipaRound_mem_beforeRound j i hij).1) =
          (output.proofData.algebraicProof.ipaRounds i).1 := by
        unfold decodedIpaQueryRepresentation
        have htarget := pinned.query.representationOfPoint_eq_of_representationsFor_eq
          final pinned.covered hselected (output.proofData.algebraicProof.ipaRounds i).1
            (List.mem_append_left _ hroundSubset.1)
        exact (pinned.query.representationOfPoint_congr _ _ _ _
          (congrArg Prod.fst hroundPoint)).trans htarget
      have hR : decodedIpaQueryRepresentation basis decoded pinned.query
          (decoded.proof.1.ipaRounds i).2
            (List.mem_append_left _
              (decoded.proof.1.ipaRound_mem_beforeRound j i hij).2) =
          (output.proofData.algebraicProof.ipaRounds i).2 := by
        unfold decodedIpaQueryRepresentation
        have htarget := pinned.query.representationOfPoint_eq_of_representationsFor_eq
          final pinned.covered hselected (output.proofData.algebraicProof.ipaRounds i).2
            (List.mem_append_left _ hroundSubset.2)
        exact (pinned.query.representationOfPoint_congr _ _ _ _
          (congrArg Prod.snd hroundPoint)).trans htarget
      have hijFin : i ≤ j := hij
      change _ = (output.proofData.adaptiveIpaCoordinates.prefix basis j).rounds i
      simp [decodedIpaQueryCoordinates, OnlineMemberProofData.adaptiveIpaCoordinates,
        AdaptiveIpaCoordinateData.prefix, hijFin, hL, hR]
    · have hijFin : ¬ i ≤ j := by
        intro h
        exact hij h
      change _ = (output.proofData.adaptiveIpaCoordinates.prefix basis j).rounds i
      simp [decodedIpaQueryCoordinates, OnlineMemberProofData.adaptiveIpaCoordinates,
        AdaptiveIpaCoordinateData.prefix, hijFin]

/-! ## Blind IPA-round surfaces -/

/-- The common-domain prefix ending at an earlier IPA round. -/
def statementEarlierRoundPrefix {pp : ProofParams}
    (t : AdaptiveActionStatementTranscript pp)
    (i : Fin (AdaptiveActionStatementShape pp).k) :
    AdaptiveActionStatementTranscript pp :=
  ⟨t.val.take (preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
        3 * (i.val + 1)), by
    rw [List.length_take]
    exact le_trans (min_le_right _ _) t.prop⟩

def statementIpaPreRecord {pp : ProofParams}
    (t : AdaptiveActionStatementTranscript pp) (O : AdaptiveActionStatementTranscript pp → Fp) :
    Fin 11 → Fp :=
  fun n => O (statementEarlierPrefix t n)

def statementIpaRoundRecord {pp : ProofParams}
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (t : AdaptiveActionStatementTranscript pp) (O : AdaptiveActionStatementTranscript pp → Fp) :
    Fin (AdaptiveActionStatementShape pp).k → Fp :=
  fun i => if _h : i.val < j.val then O (statementEarlierRoundPrefix t i) else 0

theorem statementIpaPrePrefix_ne {pp : ProofParams}
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (t : AdaptiveActionStatementTranscript pp)
    (hlen : t.val.length = preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
        3 * (j.val + 1)) (n : Fin 11) :
    statementEarlierPrefix t n ≠ t := by
  intro heq
  have hlens := congrArg (fun q : AdaptiveActionStatementTranscript pp => q.val.length) heq
  simp only [statementEarlierPrefix, List.length_take] at hlens
  have hlt : preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) n < t.val.length := by
    rw [hlen]
    fin_cases n <;> simp [preIpaLen] <;> omega
  rw [min_eq_left hlt.le] at hlens
  omega

theorem statementEarlierRoundPrefix_ne {pp : ProofParams}
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (t : AdaptiveActionStatementTranscript pp)
    (hlen : t.val.length = preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
        3 * (j.val + 1))
    (i : Fin (AdaptiveActionStatementShape pp).k) (hij : i.val < j.val) :
    statementEarlierRoundPrefix t i ≠ t := by
  intro heq
  have hlens := congrArg (fun q : AdaptiveActionStatementTranscript pp => q.val.length) heq
  simp only [statementEarlierRoundPrefix, List.length_take] at hlens
  have hlt : preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
        3 * (i.val + 1) < t.val.length := by
    rw [hlen]
    omega
  rw [min_eq_left hlt.le] at hlens
  omega

theorem statementIpaPreRecord_update_self {pp : ProofParams}
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (t : AdaptiveActionStatementTranscript pp)
    (hlen : t.val.length = preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
        3 * (j.val + 1))
    (O : AdaptiveActionStatementTranscript pp → Fp) (v : Fp) :
    statementIpaPreRecord t (Function.update O t v) = statementIpaPreRecord t O := by
  funext n
  unfold statementIpaPreRecord
  rw [Function.update_of_ne]
  exact statementIpaPrePrefix_ne j t hlen n

theorem statementIpaRoundRecord_update_self {pp : ProofParams}
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (t : AdaptiveActionStatementTranscript pp)
    (hlen : t.val.length = preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
        3 * (j.val + 1))
    (O : AdaptiveActionStatementTranscript pp → Fp) (v : Fp) :
    statementIpaRoundRecord j t (Function.update O t v) = statementIpaRoundRecord j t O := by
  funext i
  unfold statementIpaRoundRecord
  split
  · rw [Function.update_of_ne]
    exact statementEarlierRoundPrefix_ne j t hlen i (by assumption)
  · rfl

/-- At an actual selected-statement IPA point, the shorter pre-IPA views are its verifier
prefixes. -/
theorem statementIpaPreRecord_ipaPoint {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k) :
    statementIpaPreRecord
        (family.ipaPoint basis j (family.runOutput basis O)) O =
      family.runPreIpaReads basis O := by
  funext n
  unfold statementIpaPreRecord runPreIpaReads
  simp only [preIpaReadsOfOutput, preIpaReadVectorOfOutput, challengeReadVector_get]
  apply congrArg O
  apply Subtype.ext
  simpa only [statementEarlierPrefix, ipaPoint] using
    (family.runOutput basis O).prefixes_take_pre
      (family.vkTranscriptRepr basis) j n

/-- Answers at strict earlier IPA rounds agree with the selected statement's actual round reads. -/
theorem statementIpaRoundRecord_ipaPoint_before {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j i : Fin (AdaptiveActionStatementShape pp).k)
    (hij : i.val < j.val) :
    statementIpaRoundRecord j
        (family.ipaPoint basis j (family.runOutput basis O)) O i =
      family.runIpaReads basis O i := by
  unfold statementIpaRoundRecord runIpaReads
  rw [dif_pos hij]
  simp only [ipaReadsOfOutput, ipaReadVectorOfOutput, challengeReadVector_get]
  apply congrArg O
  apply Subtype.ext
  simpa only [statementEarlierRoundPrefix, ipaPoint] using
    (family.runOutput basis O).prefixes_take_round
      (family.vkTranscriptRepr basis) j i hij

/-- The round-`j` quadratic reconstructed from a decoded query and its first AGM annotation. -/
noncomputable def decodedIpaSurface {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementIpaPrefix pp j t)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (nu : Fin 11 → Fp) (chi : Fin (AdaptiveActionStatementShape pp).k → Fp) : Set Fp :=
  let ic := boundedAdaptiveStatementInstanceCommitment pp basis decoded.instanceCommitment
  let ps := adaptiveIpaCanonicalProof decoded.proof.1
  let coordinates := decodedIpaQueryCoordinates family basis decoded label
  if hcover : ∀ rho : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm (adaptiveActionStatementVk pp basis) ic ps
        (chRecord rho (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2 then
    szBadSet (adaptiveIpaRootPolynomial (adaptiveActionStatementVk pp basis) ic ps
      coordinates hcover nu chi j)
  else ∅

/-- The same quadratic computed from the adversary's final selected statement and proof. -/
noncomputable def outputIpaSurface {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (nu : Fin 11 → Fp) (chi : Fin (AdaptiveActionStatementShape pp).k → Fp) : Set Fp :=
  let ic := adaptiveActionStatementInstanceCommitment pp basis output.inputs
  let ps := adaptiveIpaCanonicalProof output.proofData.algebraicProof.erase
  let coordinates := output.proofData.adaptiveIpaCoordinates.prefix basis j
  if hcover : ∀ rho : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm (adaptiveActionStatementVk pp basis) ic ps
        (chRecord rho (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2 then
    szBadSet (adaptiveIpaRootPolynomial (adaptiveActionStatementVk pp basis) ic ps
      coordinates hcover nu chi j)
  else ∅

theorem decodedIpaSurface_measure_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementIpaPrefix pp j t)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (nu : Fin 11 → Fp) (chi : Fin (AdaptiveActionStatementShape pp).k → Fp) :
    uniformChallenge.toOuterMeasure
        (decodedIpaSurface family basis j decoded label nu chi) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  unfold decodedIpaSurface
  dsimp only
  split
  · exact adaptiveIpaRootPolynomial_measure_le _ _ _ _ _ _ _ j
  · simp

theorem outputIpaSurface_measure_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (nu : Fin 11 → Fp) (chi : Fin (AdaptiveActionStatementShape pp).k → Fp) :
    uniformChallenge.toOuterMeasure
        (outputIpaSurface family basis j output nu chi) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  unfold outputIpaSurface
  dsimp only
  split
  · exact adaptiveIpaRootPolynomial_measure_le _ _ _ _ _ _ _ j
  · simp

/-- The concrete final IPA squeeze selected by one adaptive-statement output. -/
abbrev finalIpaPoint {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k) (O : family.Coins) :
    AdaptiveActionStatementTranscript pp :=
  family.ipaPoint basis j ((family.adversary basis).run O)

/-- A pinned first round annotation makes the decoded quadratic literally the final-output
quadratic. -/
theorem decodedIpaSurface_eq_output_of_pinned {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k)
    (decoded : DecodedStatementIpaPrefix pp j
      (family.ipaPoint basis j (family.runOutput basis O)))
    (pinned : SelectedQueryRepresentationPinned
      (family.ipaPoint basis j (family.runOutput basis O))
      (family.adversary basis) O
      (ipaRepresentationTarget (family.runOutput basis O) j))
    (nu : Fin 11 → Fp) (chi : Fin (AdaptiveActionStatementShape pp).k → Fp) :
    decodedIpaSurface family basis j decoded pinned.query nu chi =
      outputIpaSurface family basis j (family.runOutput basis O) nu chi := by
  let output := family.runOutput basis O
  let outputInit := output.init (family.vkTranscriptRepr basis)
  have hinit := decoded.initialTranscript_eq_output family basis O j rfl
  have hpoint : fullPrefixes outputInit decoded.proof j =
      fullPrefixes outputInit output.toAlgebraicWfProof.proof j := by
    apply Subtype.ext
    have h := congrArg Subtype.val decoded.point_eq
    change (fullPrefixes
        (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
        decoded.proof j).val =
      (fullPrefixes outputInit output.toAlgebraicWfProof.proof j).val at h
    rw [hinit] at h
    exact h
  have hpre := preIpaTranscript_eq_of_fullPrefix_eq outputInit decoded.proof
    output.toAlgebraicWfProof.proof j hpoint
  have hsplice : decoded.proof.1 = spliceIpa output.proofData.algebraicProof.erase
      decoded.proof.1.ipaRounds decoded.proof.1.ipaC decoded.proof.1.ipaF :=
    preIpaTranscript_inj outputInit decoded.proof.2 output.proofData.wellFormed hpre
  have hcanonical : adaptiveIpaCanonicalProof decoded.proof.1 =
      adaptiveIpaCanonicalProof output.proofData.algebraicProof.erase := by
    rw [hsplice]
    rfl
  have hic := decoded.boundedInstanceCommitment_eq_output family basis O j rfl
  have hcoordinates := decodedIpaQueryCoordinates_eq_of_pinned
    family basis O j decoded pinned
  unfold decodedIpaSurface outputIpaSurface
  dsimp only
  rw [hic, hcanonical, hcoordinates]

/-- Literal-output form of `decodedIpaSurface_eq_output_of_pinned`, avoiding repeated reduction
of the `runOutput` alias inside dependent transcript indices. -/
theorem decodedIpaSurface_eq_adversary_output_of_pinned {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k)
    (decoded : DecodedStatementIpaPrefix pp j
      (family.finalIpaPoint basis j O))
    (pinned : SelectedQueryRepresentationPinned
      (family.finalIpaPoint basis j O)
      (family.adversary basis) O
      (ipaRepresentationTarget ((family.adversary basis).run O) j))
    (nu : Fin 11 → Fp) (chi : Fin (AdaptiveActionStatementShape pp).k → Fp) :
    decodedIpaSurface family basis j decoded pinned.query nu chi =
      outputIpaSurface family basis j ((family.adversary basis).run O) nu chi := by
  simpa only [ComputedAdaptiveActionStatementFSFamily.finalIpaPoint,
    ComputedAdaptiveActionStatementFSFamily.runOutput] using
    (decodedIpaSurface_eq_output_of_pinned family basis O j decoded pinned nu chi)

/-- Annotation-decoded bad set at one arbitrary IPA-round query point. -/
noncomputable def queriedIpaBad {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (t : AdaptiveActionStatementTranscript pp)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : family.Coins) : Set Fp :=
  match decodeStatementIpaPrefix? j t with
  | none => ∅
  | some decoded =>
      if t.val.length = preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
            3 * (j.val + 1) then
        decodedIpaSurface family basis j decoded label
          (statementIpaPreRecord t O) (statementIpaRoundRecord j t O)
      else ∅

/-- Fresh-query fallback bad set at one IPA round, computed from the final selected output. -/
noncomputable def outputIpaBad {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (t : AdaptiveActionStatementTranscript pp)
    (O : family.Coins) : Set Fp :=
  if t.val.length = preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
        3 * (j.val + 1) then
    outputIpaSurface family basis j output
      (statementIpaPreRecord t O) (statementIpaRoundRecord j t O)
  else ∅

/-- A named copy of the final-output IPA fallback.  Keeping this wrapper opaque during the
query/fallback case split avoids eagerly normalizing the full dependent output record. -/
noncomputable def outputIpaFallbackBad {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (t : AdaptiveActionStatementTranscript pp)
    (O : family.Coins) : Set Fp :=
  outputIpaBad family basis j output t O

/-- At a pinned final IPA query, the whole decoded bad set is the final-output fallback bad set. -/
theorem queriedIpaBad_eq_output_of_pinned {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k)
    (decoded : DecodedStatementIpaPrefix pp j
      (family.ipaPoint basis j (family.runOutput basis O)))
    (hdecode : decodeStatementIpaPrefix? j
      (family.ipaPoint basis j (family.runOutput basis O)) = some decoded)
    (pinned : SelectedQueryRepresentationPinned
      (family.ipaPoint basis j (family.runOutput basis O))
      (family.adversary basis) O
      (ipaRepresentationTarget (family.runOutput basis O) j)) :
    queriedIpaBad family basis j
        (family.ipaPoint basis j (family.runOutput basis O)) pinned.query O =
      outputIpaFallbackBad family basis j (family.runOutput basis O)
        (family.ipaPoint basis j (family.runOutput basis O)) O := by
  unfold queriedIpaBad outputIpaFallbackBad outputIpaBad
  rw [hdecode]
  dsimp only
  have hlen :
      (family.ipaPoint basis j (family.runOutput basis O)).val.length =
        preIpaLen (AdaptiveActionStatementShape pp)
            (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
          3 * (j.val + 1) := by
    simpa [ComputedAdaptiveActionStatementFSFamily.ipaPoint,
      AdaptiveActionStatementOutput.prefixes, adaptiveIpaRoundLen,
      adaptiveStatementInitLength] using
      (algebraicFullPrefixes_length_eq_adaptiveIpaRoundLen
        ((family.runOutput basis O).init (family.vkTranscriptRepr basis))
        (family.runOutput basis O).toAlgebraicWfProof j)
  rw [if_pos hlen]
  rw [if_pos hlen]
  rw [decodedIpaSurface_eq_output_of_pinned
    family basis O j decoded pinned
      (statementIpaPreRecord
        (family.ipaPoint basis j (family.runOutput basis O)) O)
      (statementIpaRoundRecord j
        (family.ipaPoint basis j (family.runOutput basis O)) O)]

theorem queriedIpaBad_update_self {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (t : AdaptiveActionStatementTranscript pp)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : family.Coins) (v : Fp) :
    queriedIpaBad family basis j t label (Function.update O t v) =
      queriedIpaBad family basis j t label O := by
  unfold queriedIpaBad
  split
  · rfl
  · split
    · rename_i decoded hdecoded hlen
      rw [statementIpaPreRecord_update_self j t hlen O v,
        statementIpaRoundRecord_update_self j t hlen O v]
    · rfl

theorem outputIpaBad_update_self {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (t : AdaptiveActionStatementTranscript pp)
    (O : family.Coins) (v : Fp) :
    outputIpaBad family basis j output t (Function.update O t v) =
      outputIpaBad family basis j output t O := by
  unfold outputIpaBad
  split
  · rename_i hlen
    rw [statementIpaPreRecord_update_self j t hlen O v,
      statementIpaRoundRecord_update_self j t hlen O v]
  · rfl

theorem outputIpaFallbackBad_update_self {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (t : AdaptiveActionStatementTranscript pp)
    (O : family.Coins) (v : Fp) :
    outputIpaFallbackBad family basis j output t (Function.update O t v) =
      outputIpaFallbackBad family basis j output t O := by
  unfold outputIpaFallbackBad
  exact outputIpaBad_update_self family basis j output t O v

theorem queriedIpaBad_measure_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (t : AdaptiveActionStatementTranscript pp)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : family.Coins) :
    uniformChallenge.toOuterMeasure (queriedIpaBad family basis j t label O) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  unfold queriedIpaBad
  split
  · simp
  · split
    · exact decodedIpaSurface_measure_le family basis j _ label _ _
    · simp

theorem outputIpaBad_measure_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (t : AdaptiveActionStatementTranscript pp)
    (O : family.Coins) :
    uniformChallenge.toOuterMeasure (outputIpaBad family basis j output t O) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  unfold outputIpaBad
  split
  · exact outputIpaSurface_measure_le family basis j output _ _
  · simp

theorem outputIpaFallbackBad_measure_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (t : AdaptiveActionStatementTranscript pp)
    (O : family.Coins) :
    uniformChallenge.toOuterMeasure
        (outputIpaFallbackBad family basis j output t O) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  unfold outputIpaFallbackBad
  exact outputIpaBad_measure_le family basis j output t O

/-- If an IPA point was never queried, its final-output bad set is the selected fallback. -/
theorem ipaBadFallback_cover {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k) (O : family.Coins)
    (t : AdaptiveActionStatementTranscript pp)
    (hbad : O t ∈
      outputIpaFallbackBad family basis j ((family.adversary basis).run O)
        t O)
    (hfind : (family.adversary basis).findLabel O t = none) :
    O t ∈
    LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
      (queriedIpaBad family basis j) (outputIpaFallbackBad family basis j)
      t O := by
  exact LabeledOracleComp.mem_firstLabelOrFallbackBad_of_findLabel_eq_none
    (family.adversary basis) (queriedIpaBad family basis j)
    (outputIpaFallbackBad family basis j) t O (O t) hfind hbad

set_option linter.constructorNameAsVariable false in
/-- The final adaptive IPA point is covered by either its first query annotation or the fresh
output fallback, unless the retained coordinates already expose an AGM relation. -/
theorem ipaBadWithoutRelation_cover {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k) (O : family.Coins)
    (hbad : O (family.ipaPoint basis j (family.runOutput basis O)) ∈
      outputIpaFallbackBad family basis j (family.runOutput basis O)
        (family.ipaPoint basis j (family.runOutput basis O)) O)
    (hnone : family.ipaRepresentationRelationFinder basis O = none) :
    O (family.ipaPoint basis j (family.runOutput basis O)) ∈
    LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
      (queriedIpaBad family basis j) (outputIpaFallbackBad family basis j)
      (family.ipaPoint basis j (family.runOutput basis O)) O := by
  by_cases hfind : (family.adversary basis).findLabel O
      (family.ipaPoint basis j (family.runOutput basis O)) = none
  · change O (family.ipaPoint basis j (family.runOutput basis O)) ∈
      outputIpaFallbackBad family basis j ((family.adversary basis).run O)
        (family.ipaPoint basis j (family.runOutput basis O)) O at hbad
    generalize (family.ipaPoint basis j (family.runOutput basis O)) = t at hfind hbad ⊢
    generalize (family.adversary basis) = A at hfind hbad ⊢
    generalize (queriedIpaBad family basis j) = bad at hbad ⊢
    generalize (outputIpaFallbackBad family basis j) = fallback at hbad ⊢
    exact LabeledOracleComp.mem_firstLabelOrFallbackBad_of_findLabel_eq_none
      A bad fallback t O (O t) hfind hbad
  · obtain ⟨label, hlabelFound⟩ := Option.isSome_iff_exists.mp
      (Option.isSome_iff_ne_none.mpr hfind)
    rw [LabeledOracleComp.firstLabelOrFallbackBad_eq_bad_of_findLabel_eq_some
      _ _ _ _ _ _ hlabelFound]
    have hat := family.ipaRepresentationRelationFinder_none_at basis O hnone j
    have hprov := selectedQueryRepresentationRelation?_eq_none
      (family.ipaPoint basis j (family.runOutput basis O))
      (family.adversary basis) O
      (ipaRepresentationTarget (family.runOutput basis O) j) _ hat
    cases hprov with
    | inl hfresh => simp [hlabelFound] at hfresh
    | inr pinned =>
        have hlabel : pinned.query = label :=
          Option.some.inj (pinned.found.symm.trans hlabelFound)
        rw [← hlabel]
        have hdecode : (decodeStatementIpaPrefix? j
            (family.ipaPoint basis j (family.runOutput basis O))).isSome :=
          family.decodeStatementIpaPrefix?_isSome basis O j
        cases hdec : decodeStatementIpaPrefix? j
            (family.ipaPoint basis j (family.runOutput basis O)) with
        | none => simp [hdec] at hdecode
        | some decoded =>
            rw [queriedIpaBad_eq_output_of_pinned
              family basis O j decoded hdec pinned]
            generalize (family.ipaPoint basis j (family.runOutput basis O)) = t at hbad ⊢
            generalize (family.runOutput basis O) = output at hbad ⊢
            generalize (outputIpaFallbackBad family basis j) = fallback at hbad ⊢
            exact hbad

/-- Each adaptive-statement IPA round retains the existing quadratic `(Q + 1)` price. -/
theorem ipaBadWithoutRelation_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | let output := family.runOutput basis O
        let t := family.ipaPoint basis j output
        O t ∈ outputIpaFallbackBad family basis j output t O ∧
          family.ipaRepresentationRelationFinder basis O = none} ≤
      (family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal)) := by
  refine family.ipaFinalBadWithoutRelation_table_le
    (Relation := AlgebraicRelationWitness (F := Fp) basis) basis j
    (outputIpaFallbackBad family basis j)
    (family.ipaRepresentationRelationFinder basis)
    (queriedIpaBad family basis j)
    (outputIpaFallbackBad family basis j)
    (fun O => ipaBadWithoutRelation_cover (pp := pp) (family := family) (basis := basis)
      (j := j) (O := O)) ?_ ?_ ?_ ?_
  · exact fun t label O v => queriedIpaBad_update_self
      family basis j t label O v
  · exact fun output t O v => outputIpaFallbackBad_update_self
      family basis j output t O v
  · exact fun t label O => queriedIpaBad_measure_le family basis j t label O
  · exact fun output t O =>
      outputIpaFallbackBad_measure_le family basis j output t O

/-! ## Adaptive-statement semantic surfaces -/

/-- Points whose coordinates affect one of the first five Action semantic challenges. -/
def DecodedStatementPrePrefix.semanticPoints {pp : ProofParams}
    {n : Fin 5} {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp (Fin.castLE (by omega) n) t) : List VestaG :=
  decoded.proof.1.actionCommitmentPointsBefore n ++
    statementInstancePoints decoded.instanceCommitment

theorem DecodedStatementPrePrefix.semanticPoints_covered {pp : ProofParams}
    {n : Fin 5} {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp (Fin.castLE (by omega) n) t) :
    ∀ P ∈ decoded.semanticPoints, P ∈ transcriptGroupPoints t.val := by
  intro P hP
  rw [DecodedStatementPrePrefix.semanticPoints, List.mem_append] at hP
  rw [← decoded.point_eq]
  rcases hP with hproof | hinstance
  · exact decoded.proof.1.actionCommitmentPointsBefore_covered
      (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
      decoded.proof.2 n P hproof
  · rw [statementInstancePoints] at hinstance
    obtain ⟨row, hrow, hcolumn⟩ := List.mem_flatten.mp hinstance
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hrow
    obtain ⟨column, hc⟩ := List.mem_ofFn.mp (hp ▸ hcolumn)
    rw [← hc]
    apply mem_transcriptGroupPoints_of_mem_point
    apply (initial_prefix_preIpaSqueezePoints
      (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
      decoded.proof.1 (Fin.castLE (by omega) n)).mem
    exact instanceCommitment_mem_initialTranscript decoded.vkTranscriptRepr
      decoded.instanceCommitment p column

/-- Query-local semantic source reconstructed from the stage prefix and its first annotation. -/
def decodedSemanticQuerySource {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    {n : Fin 5} {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp (Fin.castLE (by omega) n) t)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) :
    List (AlgebraicPoint (F := Fp) basis) :=
  label.representationsForPoints decoded.semanticPoints
      decoded.semanticPoints_covered ++
    family.fixedRepresentations basis

/-- Erasing the final semantic annotation target gives the stage proof points followed by the
selected public-instance commitments. -/
theorem semanticRepresentationTarget_points {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) (n : Fin 5) :
    (semanticRepresentationTarget output n).map AlgebraicPoint.point =
      output.toAlgebraicWfProof.proof.1.actionCommitmentPointsBefore n ++
        statementInstancePoints
          (adaptiveActionStatementInstanceCommitment pp basis output.inputs) := by
  rw [semanticRepresentationTarget, List.map_append,
    output.proofData.algebraicProof.actionRepresentationsBefore_points]
  congr 1
  unfold adaptiveStatementInstanceRepresentationList statementInstancePoints
  simp only [List.map_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  simp only [Function.comp_apply, List.map_ofFn]
  apply congrArg List.ofFn
  funext column
  exact output.instanceRepresented p column

/-- Compare one semantic stage with the complete pre-`x` source of a retained output. -/
def semanticSourceMismatchAtOfOutput? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (n : Fin 5) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  representationSourceMismatchFinder
    (output.proofData.algebraicProof.preX1AssemblySource
      (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
        family.fixedRepresentations basis))
    (semanticRepresentationTarget output n ++ family.fixedRepresentations basis)

/-- Table-indexed form of one complete-source comparison. -/
def semanticSourceMismatchAt? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 5) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let output := family.runOutput basis O
  family.semanticSourceMismatchAtOfOutput? basis output n

/-- One retained output performs all five complete-source comparisons. -/
def semanticSourceMismatchRelationFinderOfOutput {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    (List.ofFn fun n => family.semanticSourceMismatchAtOfOutput? basis output n)

/-- One finite finder covers all five comparisons using a single retained adversary output. -/
def semanticSourceMismatchRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let output := family.runOutput basis O
  family.semanticSourceMismatchRelationFinderOfOutput basis output

@[simp] theorem semanticSourceMismatchRelationFinderOfOutput_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.semanticSourceMismatchRelationFinderOfOutput basis (family.runOutput basis O) =
      family.semanticSourceMismatchRelationFinder basis O := by
  rfl

/-- No aggregate source-collision relation means every semantic-stage comparison is empty. -/
theorem semanticSourceMismatchRelationFinder_none_at {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.semanticSourceMismatchRelationFinder basis O = none)
    (n : Fin 5) :
    family.semanticSourceMismatchAt? basis O n = none := by
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hnone
  apply hall
  exact List.mem_ofFn.mpr ⟨n, rfl⟩

/-- Outside the source-collision finder, the selected stage polynomial equals deterministic
lookup in the complete pre-`x` source at every stage-covered point. -/
theorem semanticStagePolynomial_eq_full {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.semanticSourceMismatchRelationFinder basis O = none)
    (n : Fin 5) (P : VestaG)
    (hP : ∃ ap ∈ semanticRepresentationTarget (family.runOutput basis O) n ++
      family.fixedRepresentations basis, ap.point = P) :
    onlinePointPolynomial
        ((family.runOutput basis O).proofData.algebraicProof.preX1AssemblySource
          (adaptiveStatementInstanceRepresentationList
              (family.runOutput basis O).instanceRepresentations ++
            family.fixedRepresentations basis)) P =
      onlinePointPolynomial
        (semanticRepresentationTarget (family.runOutput basis O) n ++
          family.fixedRepresentations basis) P := by
  apply onlinePointPolynomial_eq_of_sourceMismatch_none
  · intro ap hap
    rw [semanticRepresentationTarget, List.append_assoc] at hap
    exact AlgebraicProofString.actionStageSource_subset_preX1AssemblySource
      (family.runOutput basis O).proofData.algebraicProof
      (adaptiveStatementInstanceRepresentationList
          (family.runOutput basis O).instanceRepresentations ++
        family.fixedRepresentations basis) n ap hap
  · exact family.semanticSourceMismatchRelationFinder_none_at basis O hnone n
  · exact hP

/-- A pinned semantic annotation reconstructs exactly the final stage source, including the
selected statement's instance representations. -/
theorem decodedSemanticQuerySource_eq_of_pinned {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 5)
    (decoded : DecodedStatementPrePrefix pp (Fin.castLE (by omega) n)
      (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O)))
    (pinned : SelectedQueryRepresentationPinned
      (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O))
      (family.adversary basis) O
      (semanticRepresentationTarget (family.runOutput basis O) n)) :
    decodedSemanticQuerySource family basis decoded pinned.query =
      semanticRepresentationTarget (family.runOutput basis O) n ++
        family.fixedRepresentations basis := by
  let output := family.runOutput basis O
  let n11 : Fin 11 := Fin.castLE (by omega) n
  let final := semanticRepresentationTarget output n
  have hinit := decoded.initialTranscript_eq_output family basis O n11 rfl
  have hprefix : preIpaSqueezePoints
        (output.init (family.vkTranscriptRepr basis)) decoded.proof.1 n11 =
      preIpaSqueezePoints (output.init (family.vkTranscriptRepr basis))
        output.toAlgebraicWfProof.proof.1 n11 := by
    have h := congrArg Subtype.val decoded.point_eq
    change (preIpaSqueezePoints
        (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
        decoded.proof.1 n11) = _ at h
    rw [hinit] at h
    exact h
  have hordinary : decoded.proof.1.actionCommitmentPointsBefore n =
      output.toAlgebraicWfProof.proof.1.actionCommitmentPointsBefore n :=
    actionCommitmentPointsBefore_eq_of_prefix
      (output.init (family.vkTranscriptRepr basis)) n _ _ hprefix
  have hinstances : statementInstancePoints decoded.instanceCommitment =
      statementInstancePoints
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs) := by
    unfold statementInstancePoints
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext p
    apply congrArg List.ofFn
    funext column
    exact decoded.instanceCommitment_eq_output family basis O n11 rfl p column
  have hpoints : decoded.semanticPoints = final.map AlgebraicPoint.point := by
    rw [DecodedStatementPrePrefix.semanticPoints, hordinary, hinstances,
      semanticRepresentationTarget_points]
  have hselected : pinned.query.representationsFor final pinned.covered = final :=
    algebraicPointList_eq_of_maps_eq
      (pinned.query.representationsFor_points final pinned.covered)
      pinned.coefficients_eq
  let decodedCovered := decoded.semanticPoints_covered
  let finalCovered : ∀ P ∈ final.map AlgebraicPoint.point,
      P ∈ transcriptGroupPoints
        (family.preIpaPoint basis n11 output).val := by
    intro P hP
    obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hP
    exact pinned.covered ap hap
  have hqueryPoints := pinned.query.representationsForPoints_congr
    decoded.semanticPoints (final.map AlgebraicPoint.point)
    decodedCovered finalCovered hpoints
  unfold decodedSemanticQuerySource
  rw [hqueryPoints,
    ← pinned.query.representationsFor_eq_representationsForPoints final pinned.covered,
    hselected]

/-- Exact semantic bad set over an explicit instance-commitment function. -/
noncomputable def adaptiveActionSurfaceAtOf {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
    (n : Fin 5) (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  let nu : Fin 11 → Fp := fun i =>
    if h : (i : Nat) < (n : Nat) then earlier ⟨i, h⟩ else 0
  let ch := chRecord nu (fun _ => 0)
  let urs := ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis
  let vk := adaptiveActionStatementVk pp basis
  let poly := adaptiveActionCommitmentPolynomialOf vk instanceCommitment ps source ch
  if _h0 : (n : Nat) = 0 then
    ↑(TopLevelLookup.thetaBadSet actionCircuit pp urs poly)
  else if _h1 : (n : Nat) = 1 then
    ↑(allResolverPermutationBetaBadSet pp.numProofs vk poly actionActiveRows) ∪
      ↑(allResolverLookupBetaBadSet pp.numProofs vk
        (ActionTerminal.semanticChRecord ch.theta 0
          (k := (AdaptiveActionStatementShape pp).k)) poly
        (actionCircuit.n - actionCircuit.blindingFactors - 2))
  else if _h2 : (n : Nat) = 2 then
    ↑(allResolverPermutationGammaBadSet pp.numProofs vk
        (ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (AdaptiveActionStatementShape pp).k)) poly actionActiveRows) ∪
      ↑(allResolverLookupGammaBadSet pp.numProofs vk
        (ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (AdaptiveActionStatementShape pp).k)) poly
        (actionCircuit.n - actionCircuit.blindingFactors - 2))
  else if _h3 : (n : Nat) = 3 then
    let model := adaptiveActionCommittedModelOf vk instanceCommitment ps source ch
      (actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
    ⋃ j, ↑(szBadSet (foldSplitWitness model.constraints actionCircuit.n j))
  else
    ↑(szBadSet (adaptiveActionPreXDifferenceOf vk instanceCommitment ps source ch
      (actionCircuit.toVerifierKey_blindingFactors_lt_n urs)))

/-! ## Pointwise prices for explicit instance commitments -/

/-- The `theta` surface price depends on the lookup layout, not the values of the explicit
instance commitments. -/
theorem adaptiveActionThetaSurfaceAtOf_measure_le {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
    (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 0 → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment 0 ps source earlier) ≤
      (TopLevelLookup.thetaBudget actionCircuit pp
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
        (adaptiveActionCommitmentPolynomialOf (adaptiveActionStatementVk pp basis)
          instanceCommitment ps source (chRecord (fun _ => 0) (fun _ => 0))) : ENNReal) /
        Fintype.card Fp := by
  simpa [adaptiveActionSurfaceAtOf] using
    (ActionTerminal.actionThetaBadSet_probability_bound pp basis
      (adaptiveActionCommitmentPolynomialOf (adaptiveActionStatementVk pp basis)
        instanceCommitment ps source (chRecord (fun _ => 0) (fun _ => 0))))

/-- The `beta` surface has the ordinary permutation/lookup price for every explicit instance
commitment function. -/
theorem adaptiveActionBetaSurfaceAtOf_measure_le {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
    (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 1 → Fp) :
    let ch : Challenges (AdaptiveActionStatementShape pp).k Fp :=
      chRecord (fun i => if h : (i : Nat) < 1 then earlier ⟨i, h⟩ else 0) (fun _ => 0)
    let poly := adaptiveActionCommitmentPolynomialOf (adaptiveActionStatementVk pp basis)
      instanceCommitment ps source ch
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment 1 ps source earlier) ≤
      ((∑ p : Fin pp.numProofs,
        (Fintype.card (ResolverPermutationCell (adaptiveActionStatementVk pp basis) poly p
          actionActiveRows) + 1) *
          Fintype.card (ResolverPermutationCell (adaptiveActionStatementVk pp basis) poly p
            actionActiveRows) : Nat) : ENNReal) / Fintype.card Fp +
      ((pp.numProofs * actionCircuit.lookupCount *
        ((actionCircuit.n - actionCircuit.blindingFactors - 2 + 2) *
          (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1) +
          (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1)) : Nat) : ENNReal) /
        Fintype.card Fp := by
  dsimp only
  simpa [adaptiveActionSurfaceAtOf, actionActiveRows,
    CircuitShape.withProofParams_numProofs,
    CircuitShape.withProofParams_numLookups] using
    (ActionTerminal.actionBetaBadSets_probability_bound pp basis (earlier 0)
      (adaptiveActionCommitmentPolynomialOf (adaptiveActionStatementVk pp basis)
        instanceCommitment ps source
        (chRecord (fun i => if h : (i : Nat) < 1 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))))

/-- The `gamma` surface likewise has a value-independent permutation/lookup price. -/
theorem adaptiveActionGammaSurfaceAtOf_measure_le {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
    (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 2 → Fp) :
    let ch : Challenges (AdaptiveActionStatementShape pp).k Fp :=
      chRecord (fun i => if h : (i : Nat) < 2 then earlier ⟨i, h⟩ else 0) (fun _ => 0)
    let poly := adaptiveActionCommitmentPolynomialOf (adaptiveActionStatementVk pp basis)
      instanceCommitment ps source ch
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment 2 ps source earlier) ≤
      ((∑ p : Fin pp.numProofs,
        2 * Fintype.card (ResolverPermutationCell
          (adaptiveActionStatementVk pp basis) poly p actionActiveRows) : Nat) : ENNReal) /
          Fintype.card Fp +
      ((pp.numProofs * actionCircuit.lookupCount *
        (2 * (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1)) : Nat) : ENNReal) /
          Fintype.card Fp := by
  dsimp only
  simpa [adaptiveActionSurfaceAtOf, actionActiveRows,
    CircuitShape.withProofParams_numProofs,
    CircuitShape.withProofParams_numLookups] using
    (ActionTerminal.actionGammaBadSets_probability_bound pp basis (earlier 0)
      (earlier ⟨1, by omega⟩)
      (adaptiveActionCommitmentPolynomialOf (adaptiveActionStatementVk pp basis)
        instanceCommitment ps source
        (chRecord (fun i => if h : (i : Nat) < 2 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))))

/-- The `y` surface depends only on the explicit committed model's constraint count. -/
theorem adaptiveActionYSurfaceAtOf_measure_le {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
    (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 3 → Fp)
    (hn : actionCircuit.n ≠ 0) :
    let ch : Challenges (AdaptiveActionStatementShape pp).k Fp :=
      chRecord (fun i => if h : (i : Nat) < 3 then earlier ⟨i, h⟩ else 0) (fun _ => 0)
    let model := adaptiveActionCommittedModelOf (adaptiveActionStatementVk pp basis)
      instanceCommitment ps source ch
      (actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis))
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment 3 ps source earlier) ≤
      ((actionCircuit.n * model.constraints.length : Nat) : ENNReal) /
        Fintype.card Fp := by
  dsimp only
  simpa [adaptiveActionSurfaceAtOf] using
    (ActionTerminal.actionYBadSet_probability_bound
      (adaptiveActionCommittedModelOf (adaptiveActionStatementVk pp basis)
        instanceCommitment ps source
        (chRecord (fun i => if h : (i : Nat) < 3 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))
        (actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis))).constraints hn)

/-- The `x` surface is the Schwartz--Zippel set of the explicit pre-`x` difference. -/
theorem adaptiveActionXSurfaceAtOf_measure_le {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
    (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 4 → Fp) :
    let ch : Challenges (AdaptiveActionStatementShape pp).k Fp :=
      chRecord (fun i => if h : (i : Nat) < 4 then earlier ⟨i, h⟩ else 0) (fun _ => 0)
    let difference := adaptiveActionPreXDifferenceOf (adaptiveActionStatementVk pp basis)
      instanceCommitment ps source ch
      (actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis))
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment 4 ps source earlier) ≤
      (difference.natDegree : ENNReal) / Fintype.card Fp := by
  dsimp only
  simpa [adaptiveActionSurfaceAtOf] using
    (uniformChallenge_szBadSet
      (adaptiveActionPreXDifferenceOf (adaptiveActionStatementVk pp basis)
        instanceCommitment ps source
        (chRecord (fun i => if h : (i : Nat) < 4 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))
        (actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis))))

/-- The explicit-instance surface specializes to the existing Action surface. -/
theorem adaptiveActionSurfaceAtOf_action {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp) (n : Fin 5)
    (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (n : Nat) → Fp) :
    adaptiveActionSurfaceAtOf basis
        (adaptiveActionStatementInstanceCommitment pp basis inputs) n ps source earlier =
      adaptiveActionSurfaceAt pp basis inputs n ps source earlier := by
  rfl

noncomputable def decodedSemanticSurface {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 5) {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp (Fin.castLE (by omega) n) t)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  adaptiveActionSurfaceAtOf basis
    (boundedAdaptiveStatementInstanceCommitment pp basis decoded.instanceCommitment)
    n decoded.proof.1 (decodedSemanticQuerySource family basis decoded label) earlier

noncomputable def outputSemanticSurface {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 5)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  adaptiveActionSurfaceAtOf basis
    (adaptiveActionStatementInstanceCommitment pp basis output.inputs) n
    output.toAlgebraicWfProof.proof.1
    (semanticRepresentationTarget output n ++ family.fixedRepresentations basis) earlier

/-- A pinned first annotation makes the explicit query-time semantic surface equal the actual
selected-statement surface. -/
theorem decodedSemanticSurface_eq_output_of_pinned {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 5)
    (decoded : DecodedStatementPrePrefix pp (Fin.castLE (by omega) n)
      (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O)))
    (pinned : SelectedQueryRepresentationPinned
      (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O))
      (family.adversary basis) O
      (semanticRepresentationTarget (family.runOutput basis O) n))
    (earlier : Fin (n : Nat) → Fp) :
    decodedSemanticSurface family basis n decoded pinned.query earlier =
      outputSemanticSurface family basis n (family.runOutput basis O) earlier := by
  let output := family.runOutput basis O
  let n11 : Fin 11 := Fin.castLE (by omega) n
  have hinit := decoded.initialTranscript_eq_output family basis O n11 rfl
  have hprefix : preIpaSqueezePoints
        (output.init (family.vkTranscriptRepr basis)) decoded.proof.1 n11 =
      preIpaSqueezePoints (output.init (family.vkTranscriptRepr basis))
        output.toAlgebraicWfProof.proof.1 n11 := by
    have h := congrArg Subtype.val decoded.point_eq
    change (preIpaSqueezePoints
        (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
        decoded.proof.1 n11) = _ at h
    rw [hinit] at h
    exact h
  have hic := decoded.boundedInstanceCommitment_eq_output family basis O n11 rfl
  have hsource := decodedSemanticQuerySource_eq_of_pinned
    family basis O n decoded pinned
  unfold decodedSemanticSurface outputSemanticSurface
  rw [hic, adaptiveActionSurfaceAtOf_action, adaptiveActionSurfaceAtOf_action]
  exact adaptiveActionSurfaceAt_congr pp
    (output.init (family.vkTranscriptRepr basis)) basis output.inputs n
    decoded.proof.1 output.toAlgebraicWfProof.proof.1 decoded.proof.2
    output.toAlgebraicWfProof.proof.2 _ _ earlier hprefix hsource

/-- Annotation-decoded semantic bad set at one arbitrary query point. -/
noncomputable def queriedSemanticBad {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 5) (t : AdaptiveActionStatementTranscript pp)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : family.Coins) : Set Fp :=
  let n11 : Fin 11 := Fin.castLE (by omega) n
  match decodeStatementPrePrefix? n11 t with
  | none => ∅
  | some decoded =>
      if t.val.length = preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) n11 then
        decodedSemanticSurface family basis n decoded label
          (fun i => O (statementEarlierPrefix t (i.castLE (le_of_lt n11.isLt))))
      else ∅

noncomputable def outputSemanticBad {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 5)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (t : AdaptiveActionStatementTranscript pp) (O : family.Coins) : Set Fp :=
  let n11 : Fin 11 := Fin.castLE (by omega) n
  if t.val.length = preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) n11 then
    outputSemanticSurface family basis n output
      (fun i => O (statementEarlierPrefix t (i.castLE (le_of_lt n11.isLt))))
  else ∅

theorem queriedSemanticBad_update_self {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 5) (t : AdaptiveActionStatementTranscript pp)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : family.Coins) (v : Fp) :
    queriedSemanticBad family basis n t label (Function.update O t v) =
      queriedSemanticBad family basis n t label O := by
  unfold queriedSemanticBad
  dsimp only
  split
  · rfl
  · split
    · rename_i decoded hdecoded hlen
      congr 1
      funext i
      rw [Function.update_of_ne]
      exact statementEarlierPrefix_ne (Fin.castLE (by omega) n) t hlen i
    · rfl

theorem outputSemanticBad_update_self {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 5)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (t : AdaptiveActionStatementTranscript pp) (O : family.Coins) (v : Fp) :
    outputSemanticBad family basis n output t (Function.update O t v) =
      outputSemanticBad family basis n output t O := by
  unfold outputSemanticBad
  dsimp only
  split
  · rename_i hlen
    congr 1
    funext i
    rw [Function.update_of_ne]
    exact statementEarlierPrefix_ne (Fin.castLE (by omega) n) t hlen i
  · rfl

theorem queriedSemanticBad_measure_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 5) (t : AdaptiveActionStatementTranscript pp)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t) (O : family.Coins)
    {epsilon : ENNReal}
    (hsurface : ∀
      (instanceCommitment :
        Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
      (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ epsilon) :
    uniformChallenge.toOuterMeasure (queriedSemanticBad family basis n t label O) ≤
      epsilon := by
  unfold queriedSemanticBad
  dsimp only
  split
  · simp
  · split
    · exact hsurface _ _ _ _
    · simp

theorem outputSemanticBad_measure_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 5)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (t : AdaptiveActionStatementTranscript pp) (O : family.Coins)
    {epsilon : ENNReal}
    (hsurface : ∀
      (instanceCommitment :
        Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
      (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ epsilon) :
    uniformChallenge.toOuterMeasure
      (outputSemanticBad family basis n output t O) ≤ epsilon := by
  unfold outputSemanticBad
  dsimp only
  split
  · exact hsurface _ _ _ _
  · simp

/-- A pinned annotation puts the final semantic surface inside the query-time decoded set. -/
private theorem mem_queriedSemanticBad_of_pinned {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 5)
    (pinned : SelectedQueryRepresentationPinned
      (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O))
      (family.adversary basis) O
      (semanticRepresentationTarget (family.runOutput basis O) n))
    (hbad : O (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O)) ∈
      outputSemanticBad family basis n (family.runOutput basis O)
        (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O)) O) :
    O (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O)) ∈
      queriedSemanticBad family basis n
        (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O))
        pinned.query O := by
  have hdecode := family.decodeStatementPrePrefix?_isSome basis O (Fin.castLE (by omega) n)
  change (decodeStatementPrePrefix? (Fin.castLE (by omega) n)
    (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O))).isSome
    at hdecode
  cases hdec : decodeStatementPrePrefix? (Fin.castLE (by omega) n)
      (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O)) with
  | none => simp [hdec] at hdecode
  | some decoded =>
      unfold queriedSemanticBad
      dsimp only
      rw [hdec]
      dsimp only
      have hlen : (family.preIpaPoint basis (Fin.castLE (by omega) n)
          (family.runOutput basis O)).val.length =
          preIpaLen (AdaptiveActionStatementShape pp)
            (adaptiveStatementInitLength (AdaptiveActionStatementShape pp))
            (Fin.castLE (by omega) n) := by
        simpa [ComputedAdaptiveActionStatementFSFamily.preIpaPoint,
          AdaptiveActionStatementOutput.prefixesPre,
          adaptiveStatementInitLength] using
          (preIpaSqueezePoints_length_eq
            ((family.runOutput basis O).init (family.vkTranscriptRepr basis))
            (family.runOutput basis O).toAlgebraicWfProof.proof.1
            (family.runOutput basis O).toAlgebraicWfProof.proof.2 (Fin.castLE (by omega) n))
      rw [if_pos hlen]
      rw [decodedSemanticSurface_eq_output_of_pinned family basis O n decoded pinned]
      unfold outputSemanticBad at hbad
      dsimp only at hbad
      split at hbad
      all_goals exact hbad

/-- One adaptive selected-statement semantic squeeze uses the existing `(Q + 1)` query price. -/
theorem semanticBadWithoutRelation_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 5) {epsilon : ENNReal}
    (hsurface : ∀
      (instanceCommitment :
        Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
      (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ epsilon) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | let output := family.runOutput basis O
        let n11 : Fin 11 := Fin.castLE (by omega) n
        let t := family.preIpaPoint basis n11 output
        O t ∈ outputSemanticBad family basis n output t O ∧
          family.semanticRepresentationRelationFinder basis O = none} ≤
      (family.Q + 1 : Nat) * epsilon := by
  let n11 : Fin 11 := Fin.castLE (by omega) n
  apply family.preIpaFinalBadWithoutRelation_table_le basis n11
    (outputSemanticBad family basis n)
    (family.semanticRepresentationRelationFinder basis)
    (queriedSemanticBad family basis n)
    (outputSemanticBad family basis n)
  · intro O
    dsimp only
    intro hbad hnone
    change O (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O)) ∈
      LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
        (queriedSemanticBad family basis n) (outputSemanticBad family basis n)
        (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O)) O
    unfold LabeledOracleComp.firstLabelOrFallbackBad
    cases hfind : (family.adversary basis).findLabel O
        (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O)) with
    | none => simpa [hfind] using hbad
    | some label =>
        have hat := family.semanticRepresentationRelationFinder_none_at basis O hnone n
        have hprov := selectedQueryRepresentationRelation?_eq_none
          (family.preIpaPoint basis (Fin.castLE (by omega) n) (family.runOutput basis O))
          (family.adversary basis) O
          (semanticRepresentationTarget (family.runOutput basis O) n) _ hat
        cases hprov with
        | inl hfresh => simp [hfind] at hfresh
        | inr pinned =>
            have hlabel : pinned.query = label :=
              Option.some.inj (pinned.found.symm.trans hfind)
            subst label
            exact mem_queriedSemanticBad_of_pinned family basis O n pinned
              (by simpa using hbad)
  · exact fun t label O v => queriedSemanticBad_update_self
      family basis n t label O v
  · exact fun output t O v => outputSemanticBad_update_self
      family basis n output t O v
  · exact fun t label O => queriedSemanticBad_measure_le
      family basis n t label O hsurface
  · exact fun output t O => outputSemanticBad_measure_le
      family basis n output t O hsurface

/-! ## Deployed-root surfaces -/

/-- A query-time deployed-root surface decoded from one adaptive statement prefix. -/
noncomputable def decodedRootSurface {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11) (h5n : 5 ≤ (n : Nat))
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp n t)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  adaptiveRootSurfaceAt (adaptiveActionStatementVk pp basis)
    (boundedAdaptiveStatementInstanceCommitment pp basis decoded.instanceCommitment) n
    (adaptiveRootPrefixProof n decoded.proof.1)
    (decodedRootQuerySource family basis h5n decoded label) earlier

/-- Every decoded root surface has the existing direct-route pointwise budget. -/
theorem decodedRootSurface_measure_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11) (h5n : 5 ≤ (n : Nat))
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp n t)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (earlier : Fin (n : Nat) → Fp) :
    uniformChallenge.toOuterMeasure
        (decodedRootSurface family basis n h5n decoded label earlier) ≤
      deployedRootEventBudget (AdaptiveActionStatementShape pp)
        (adaptiveRootEventIndex n) := by
  exact adaptiveRootSurfaceAt_measure_le _ _ n h5n _ _ earlier

/-- The final-output root surface at one actual adaptive statement. -/
noncomputable def outputRootSurface {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  adaptiveRootSurfaceAt (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis output.inputs) n
    (adaptiveRootPrefixProof n output.toAlgebraicWfProof.proof.1)
    (preIpaRepresentationTarget output n ++ family.fixedRepresentations basis) earlier

/-- The witness `x₄` coefficient columns, rewritten to the adaptive representation walk. -/
private theorem batchWitness_x4Coeffs_adaptive {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {view : RunView pp family basis} (witness : family.BatchWitnessV basis view)
    (qCovered : CommitmentRefCovered
      [view.output.proofData.algebraicProof.multiopenQPrime]
      (.point view.output.proofData.algebraicProof.erase.multiopenQPrime)) :
    witness.batches.x4.coeffs =
      (adaptiveX4ColumnRepresentations (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.proofData.algebraicProof.erase
        (view.output.proofData.algebraicProof.preX1AssemblySource
          (adaptiveStatementInstanceRepresentationList
              view.output.instanceRepresentations ++
            family.fixedRepresentations basis))
        [view.output.proofData.algebraicProof.multiopenQPrime]
        view.output.proofData.adaptivePreX1MembersCovered qCovered
        view.pre).coeffs :=
  witness.x4Coeffs.trans
    ((view.output.proofData.adaptiveX4Columns_eq_deployed
      view.pre).1.symm)

/-- The witness `x₄` augmented `u` columns, rewritten to the adaptive representation walk. -/
private theorem batchWitness_x4U_adaptive {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {view : RunView pp family basis} (witness : family.BatchWitnessV basis view)
    (qCovered : CommitmentRefCovered
      [view.output.proofData.algebraicProof.multiopenQPrime]
      (.point view.output.proofData.algebraicProof.erase.multiopenQPrime)) :
    witness.batches.x4.uComp =
      (adaptiveX4ColumnRepresentations (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.proofData.algebraicProof.erase
        (view.output.proofData.algebraicProof.preX1AssemblySource
          (adaptiveStatementInstanceRepresentationList
              view.output.instanceRepresentations ++
            family.fixedRepresentations basis))
        [view.output.proofData.algebraicProof.multiopenQPrime]
        view.output.proofData.adaptivePreX1MembersCovered qCovered
        view.pre).uComp :=
  witness.x4U.trans
    ((view.output.proofData.adaptiveX4Columns_eq_deployed
      view.pre).2.1.symm)

/-- The witness member columns, rewritten to the adaptive representation walk. -/
private theorem batchWitness_members_adaptive {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {view : RunView pp family basis} (witness : family.BatchWitnessV basis view) :
    ∀ i (hi : i < deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.proofData.algebraicProof.erase
      (chRecord view.pre (fun _ => 0))),
      (witness.batches.x1 i hi).coeffs =
        (adaptiveMemberRepresentations (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            view.output.inputs)
          view.output.proofData.algebraicProof.erase
          (view.output.proofData.algebraicProof.preX1AssemblySource
            (adaptiveStatementInstanceRepresentationList
                view.output.instanceRepresentations ++
              family.fixedRepresentations basis))
          view.output.proofData.adaptivePreX1MembersCovered
          view.pre i hi).coeffs := by
  intro i hi
  exact (witness.memberCoeffs i hi).trans
    ((view.output.proofData.adaptiveMemberRepresentations_eq_deployed
      view.pre i hi).1.symm)

/-- The adaptive aggregate reconstructs the selected proof's canonical aggregate. -/
private theorem batchWitness_aggregate_adaptive {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {view : RunView pp family basis} (witness : family.BatchWitnessV basis view)
    (qCovered : CommitmentRefCovered
      [view.output.proofData.algebraicProof.multiopenQPrime]
      (.point view.output.proofData.algebraicProof.erase.multiopenQPrime)) :
    adaptiveAggregateG (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.proofData.algebraicProof.erase
      (view.output.proofData.algebraicProof.preX1AssemblySource
        (adaptiveStatementInstanceRepresentationList
            view.output.instanceRepresentations ++
          family.fixedRepresentations basis))
      [view.output.proofData.algebraicProof.multiopenQPrime]
      view.output.proofData.adaptivePreX1MembersCovered qCovered
      view.pre =
        view.output.proofData.toAlgebraicWfProof.aMulti
          view.pre := by
  unfold adaptiveAggregateG
  dsimp only
  rw [(view.output.proofData.adaptiveX4Columns_eq_deployed
    view.pre).1]
  exact witness.x4Source_reconstruct

/-- The adaptive aggregate `u` coordinate reconstructs the selected proof's. -/
private theorem batchWitness_aggregateU_adaptive {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {view : RunView pp family basis} (witness : family.BatchWitnessV basis view)
    (qCovered : CommitmentRefCovered
      [view.output.proofData.algebraicProof.multiopenQPrime]
      (.point view.output.proofData.algebraicProof.erase.multiopenQPrime)) :
    adaptiveAggregateU (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.proofData.algebraicProof.erase
      (view.output.proofData.algebraicProof.preX1AssemblySource
        (adaptiveStatementInstanceRepresentationList
            view.output.instanceRepresentations ++
          family.fixedRepresentations basis))
      [view.output.proofData.algebraicProof.multiopenQPrime]
      view.output.proofData.adaptivePreX1MembersCovered qCovered
      view.pre =
        view.output.proofData.toAlgebraicWfProof.multiU
          view.pre := by
  unfold adaptiveAggregateU
  dsimp only
  rw [(view.output.proofData.adaptiveX4Columns_eq_deployed
    view.pre).2.1]
  exact witness.x4Source_reconstructU

/-- The direct batch witness identifies all six normalized online root sets with the executable
root checks used by the adaptive-statement terminal. -/
theorem BatchWitnessV.rootSets_eq {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {view : RunView pp family basis} (witness : family.BatchWitnessV basis view) :
    let output := view.output
    let data := output.proofData
    let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
      family.fixedRepresentations basis
    let nu := view.pre
    adaptiveX1AllRootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        data.adaptivePreX1MembersCovered nu =
      deployedX1AllRootSet (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
        (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (chRecord nu (fun _ => 0)) witness.batches ∧
    adaptiveX2RootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        data.adaptivePreX1MembersCovered nu =
      deployedX2RootSet (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
        (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (chRecord nu (fun _ => 0)) witness.batches ∧
    adaptiveX3RootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
      deployedX3RootSet (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
        (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (chRecord nu (fun _ => 0)) witness.batches ∧
    adaptiveX4RootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
      deployedX4RootSet (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
        (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (chRecord nu (fun _ => 0)) witness.batches ∧
    adaptiveXiRootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨data.algebraicProof.ipaS, by simp, rfl⟩ nu =
      szBadSet (ipaShiftXiPolynomial
        (commitGen (evalVector (AdaptiveActionStatementShape pp).k (nu 7))
            (data.toAlgebraicWfProof.aMulti nu) -
          multiopenValue (adaptiveActionStatementVk pp basis)
            (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
            data.algebraicProof.erase (chRecord nu (fun _ => 0)))
        (commitGen (evalVector (AdaptiveActionStatementShape pp).k (nu 7))
          data.toAlgebraicWfProof.s)) ∧
    adaptiveZRootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨data.algebraicProof.ipaS, by simp, rfl⟩ nu =
      szBadSet (ipaShiftZPolynomial
        (commitGen (evalVector (AdaptiveActionStatementShape pp).k (nu 7))
            (data.toAlgebraicWfProof.aMulti nu) -
          multiopenValue (adaptiveActionStatementVk pp basis)
            (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
            data.algebraicProof.erase (chRecord nu (fun _ => 0)))
        (data.toAlgebraicWfProof.multiU nu) data.toAlgebraicWfProof.sU
        (commitGen (evalVector (AdaptiveActionStatementShape pp).k (nu 7))
          data.toAlgebraicWfProof.s) (nu 9)) := by
  dsimp only
  refine ⟨view.output.proofData.adaptiveX1AllRootSet_eq_deployed
    view.pre witness.batches (batchWitness_members_adaptive witness), ?_⟩
  refine ⟨view.output.proofData.adaptiveX2RootSet_eq_deployed
    view.pre ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩ witness.batches
    (batchWitness_x4Coeffs_adaptive witness ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩), ?_⟩
  refine ⟨view.output.proofData.adaptiveX3RootSet_eq_deployed
    view.pre ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩ witness.batches
    (batchWitness_x4Coeffs_adaptive witness ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩), ?_⟩
  refine ⟨view.output.proofData.adaptiveX4RootSet_eq_deployed
    view.pre ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩ witness.batches
    (batchWitness_x4Coeffs_adaptive witness ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩), ?_⟩
  have hshift := view.output.proofData.adaptiveShiftRootSets_eq
    view.pre
    ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩
    ⟨view.output.proofData.algebraicProof.ipaS, by simp, rfl⟩
    witness.batches.x4 (batchWitness_x4Coeffs_adaptive witness ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩)
    (batchWitness_x4U_adaptive witness ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩) (batchWitness_aggregate_adaptive witness ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩)
    (batchWitness_aggregateU_adaptive witness ⟨view.output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩)
  exact ⟨hshift.1, hshift.2⟩


/-- Every final-output root surface has the same pointwise budget. -/
theorem outputRootSurface_measure_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11) (h5n : 5 ≤ (n : Nat))
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (earlier : Fin (n : Nat) → Fp) :
    uniformChallenge.toOuterMeasure
        (outputRootSurface family basis n output earlier) ≤
      deployedRootEventBudget (AdaptiveActionStatementShape pp)
        (adaptiveRootEventIndex n) := by
  exact adaptiveRootSurfaceAt_measure_le _ _ n h5n _ _ earlier

/-- A pinned first annotation makes the decoded root surface literally the final-output surface. -/
theorem decodedRootSurface_eq_output_of_pinned {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11) (h5n : 5 ≤ (n : Nat))
    (decoded : DecodedStatementPrePrefix pp n
      (family.preIpaPoint basis n (family.runOutput basis O)))
    (pinned : SelectedQueryRepresentationPinned
      (family.preIpaPoint basis n (family.runOutput basis O))
      (family.adversary basis) O
      (preIpaRepresentationTarget (family.runOutput basis O) n))
    (earlier : Fin (n : Nat) → Fp) :
    decodedRootSurface family basis n h5n decoded pinned.query earlier =
      outputRootSurface family basis n (family.runOutput basis O) earlier := by
  let output := family.runOutput basis O
  have hinit := decoded.initialTranscript_eq_output family basis O n rfl
  have hprefix : preIpaSqueezePoints
        (output.init (family.vkTranscriptRepr basis)) decoded.proof.1 n =
      preIpaSqueezePoints (output.init (family.vkTranscriptRepr basis))
        output.toAlgebraicWfProof.proof.1 n := by
    have h := congrArg Subtype.val decoded.point_eq
    change (preIpaSqueezePoints
        (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
        decoded.proof.1 n) = _ at h
    rw [hinit] at h
    exact h
  have hproof := adaptiveRootPrefixProof_congr
    (output.init (family.vkTranscriptRepr basis)) n h5n
    decoded.proof.1 output.toAlgebraicWfProof.proof.1
    decoded.proof.2 output.toAlgebraicWfProof.proof.2 hprefix
  unfold decodedRootSurface outputRootSurface
  rw [decoded.boundedInstanceCommitment_eq_output family basis O n rfl,
    decodedRootQuerySource_eq_of_pinned family basis O n h5n decoded pinned,
    hproof]

/-- Annotation-decoded bad set used at one arbitrary root-query point. -/
noncomputable def queriedRootBad {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11) (h5n : 5 ≤ (n : Nat))
    (t : AdaptiveActionStatementTranscript pp)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : family.Coins) : Set Fp :=
  match decodeStatementPrePrefix? n t with
  | none => ∅
  | some decoded =>
      if t.val.length = preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) n then
        decodedRootSurface family basis n h5n decoded label
          (fun i => O (statementEarlierPrefix t (i.castLE (le_of_lt n.isLt))))
      else ∅

/-- Fresh-query fallback bad set computed from the adversary's final output. -/
noncomputable def outputRootBad {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (t : AdaptiveActionStatementTranscript pp)
    (O : family.Coins) : Set Fp :=
  statementPrefixBad n
    (fun _ earlier => outputRootSurface family basis n output earlier) t O

theorem queriedRootBad_update_self {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11) (h5n : 5 ≤ (n : Nat))
    (t : AdaptiveActionStatementTranscript pp)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : family.Coins) (v : Fp) :
    queriedRootBad family basis n h5n t label (Function.update O t v) =
      queriedRootBad family basis n h5n t label O := by
  unfold queriedRootBad
  split
  · rfl
  · split
    · rename_i decoded hdecoded hlen
      congr 1
      funext i
      rw [Function.update_of_ne]
      exact statementEarlierPrefix_ne n t hlen i
    · rfl

theorem outputRootBad_update_self {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (t : AdaptiveActionStatementTranscript pp)
    (O : family.Coins) (v : Fp) :
    outputRootBad family basis n output t (Function.update O t v) =
      outputRootBad family basis n output t O := by
  exact statementPrefixBad_update_self n _ t O v

theorem queriedRootBad_measure_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11) (h5n : 5 ≤ (n : Nat))
    (t : AdaptiveActionStatementTranscript pp)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : family.Coins) :
    uniformChallenge.toOuterMeasure
        (queriedRootBad family basis n h5n t label O) ≤
      deployedRootEventBudget (AdaptiveActionStatementShape pp)
        (adaptiveRootEventIndex n) := by
  unfold queriedRootBad
  split
  · simp
  · split
    · exact decodedRootSurface_measure_le family basis n h5n _ label _
    · simp

theorem outputRootBad_measure_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11) (h5n : 5 ≤ (n : Nat))
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (t : AdaptiveActionStatementTranscript pp)
    (O : family.Coins) :
    uniformChallenge.toOuterMeasure (outputRootBad family basis n output t O) ≤
      deployedRootEventBudget (AdaptiveActionStatementShape pp)
        (adaptiveRootEventIndex n) := by
  exact statementPrefixBad_measure_le n _
    (fun _ earlier => outputRootSurface_measure_le family basis n h5n output earlier) t O

/-- A pinned annotation puts the final root surface inside the query-time decoded set. -/
private theorem mem_queriedRootBad_of_pinned {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11) (h5n : 5 ≤ (n : Nat))
    (pinned : SelectedQueryRepresentationPinned
      (family.preIpaPoint basis n (family.runOutput basis O))
      (family.adversary basis) O
      (preIpaRepresentationTarget (family.runOutput basis O) n))
    (hbad : O (family.preIpaPoint basis n (family.runOutput basis O)) ∈
      outputRootBad family basis n (family.runOutput basis O)
        (family.preIpaPoint basis n (family.runOutput basis O)) O) :
    O (family.preIpaPoint basis n (family.runOutput basis O)) ∈
      queriedRootBad family basis n h5n
        (family.preIpaPoint basis n (family.runOutput basis O)) pinned.query O := by
  have hdecode := family.decodeStatementPrePrefix?_isSome basis O n
  change (decodeStatementPrePrefix? n
    (family.preIpaPoint basis n (family.runOutput basis O))).isSome at hdecode
  cases hdec : decodeStatementPrePrefix? n
      (family.preIpaPoint basis n (family.runOutput basis O)) with
  | none => simp [hdec] at hdecode
  | some decoded =>
      unfold queriedRootBad
      rw [hdec]
      dsimp only
      have hlen : (family.preIpaPoint basis n (family.runOutput basis O)).val.length =
          preIpaLen (AdaptiveActionStatementShape pp)
            (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) n := by
        simpa [ComputedAdaptiveActionStatementFSFamily.preIpaPoint,
          AdaptiveActionStatementOutput.prefixesPre,
          adaptiveStatementInitLength] using
          (preIpaSqueezePoints_length_eq
            ((family.runOutput basis O).init (family.vkTranscriptRepr basis))
            (family.runOutput basis O).toAlgebraicWfProof.proof.1
            (family.runOutput basis O).toAlgebraicWfProof.proof.2 n)
      rw [if_pos hlen]
      rw [decodedRootSurface_eq_output_of_pinned family basis O n h5n decoded pinned]
      unfold outputRootBad statementPrefixBad at hbad
      split at hbad
      all_goals exact hbad

/-- Each actual adaptive-statement root event retains the direct `(Q + 1)` squeeze price. -/
theorem rootBadWithoutRelation_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (n : Fin 11) (h5n : 5 ≤ (n : Nat)) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | let output := family.runOutput basis O
        let t := family.preIpaPoint basis n output
        O t ∈ outputRootBad family basis n output t O ∧
          family.preIpaRepresentationRelationFinder basis O = none} ≤
      (family.Q + 1 : Nat) *
        deployedRootEventBudget (AdaptiveActionStatementShape pp)
          (adaptiveRootEventIndex n) := by
  apply family.preIpaFinalBadWithoutRelation_table_le basis n
    (outputRootBad family basis n)
    (family.preIpaRepresentationRelationFinder basis)
    (queriedRootBad family basis n h5n)
    (outputRootBad family basis n)
  · intro O
    dsimp only
    intro hbad hnone
    change O (family.preIpaPoint basis n (family.runOutput basis O)) ∈
      LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
        (queriedRootBad family basis n h5n) (outputRootBad family basis n)
        (family.preIpaPoint basis n (family.runOutput basis O)) O
    unfold LabeledOracleComp.firstLabelOrFallbackBad
    cases hfind : (family.adversary basis).findLabel O
        (family.preIpaPoint basis n (family.runOutput basis O)) with
    | none => simpa [hfind] using hbad
    | some label =>
        have hat := family.preIpaRepresentationRelationFinder_none_at basis O hnone n h5n
        have hprov := selectedQueryRepresentationRelation?_eq_none
          (family.preIpaPoint basis n (family.runOutput basis O))
          (family.adversary basis) O
          (preIpaRepresentationTarget (family.runOutput basis O) n) _ hat
        cases hprov with
        | inl hfresh => simp [hfind] at hfresh
        | inr pinned =>
            have hlabel : pinned.query = label :=
              Option.some.inj (pinned.found.symm.trans hfind)
            subst label
            exact mem_queriedRootBad_of_pinned family basis O n h5n pinned
              (by simpa using hbad)
  · exact fun t label O v => queriedRootBad_update_self
      family basis n h5n t label O v
  · exact fun output t O v => outputRootBad_update_self
      family basis n output t O v
  · exact fun t label O => queriedRootBad_measure_le
      family basis n h5n t label O
  · exact fun output t O => outputRootBad_measure_le
      family basis n h5n output t O

/-! ## Actual selected-statement surface identities -/

/-- The full-coordinate assembly coverage supplied by the adversary's output. -/
private theorem outputIpaAssemblyCovered {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        (adaptiveIpaCanonicalProof output.proofData.algebraicProof.erase)
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ output.proofData.adaptiveIpaCoordinates.multiopenSource, ap.point = pr.2 :=
  fun rho pr hpr => output.proofData.assemblyCovered rho pr hpr

/-- The decoded prefix-coordinate polynomial is its full-assembly form. -/
private theorem outputIpaPolynomial_prefix_step {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (nu : Fin 11 → Fp) (chi' : Fin (AdaptiveActionStatementShape pp).k → Fp)
    (hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        (adaptiveIpaCanonicalProof output.proofData.algebraicProof.erase)
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ (output.proofData.adaptiveIpaCoordinates.prefix basis j).multiopenSource,
          ap.point = pr.2) :
    adaptiveIpaRootPolynomial (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        (adaptiveIpaCanonicalProof output.proofData.algebraicProof.erase)
        (output.proofData.adaptiveIpaCoordinates.prefix basis j) hcover nu chi' j =
      adaptiveIpaRootPolynomial (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        (adaptiveIpaCanonicalProof output.proofData.algebraicProof.erase)
        output.proofData.adaptiveIpaCoordinates
        (outputIpaAssemblyCovered family basis output) nu chi' j :=
  adaptiveIpaRootPolynomial_prefix _ _ _ _ _ _ _ j

/-- The polynomial reads only rounds below `j`: any record agreeing there yields it unchanged. -/
private theorem outputIpaPolynomial_chi_step {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (nu : Fin 11 → Fp)
    (chi' chi : Fin (AdaptiveActionStatementShape pp).k → Fp)
    (hchi : ∀ i, i.val < j.val → chi' i = chi i) :
    adaptiveIpaRootPolynomial (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        (adaptiveIpaCanonicalProof output.proofData.algebraicProof.erase)
        output.proofData.adaptiveIpaCoordinates
        (outputIpaAssemblyCovered family basis output) nu chi' j =
      adaptiveIpaRootPolynomial (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        (adaptiveIpaCanonicalProof output.proofData.algebraicProof.erase)
        output.proofData.adaptiveIpaCoordinates
        (outputIpaAssemblyCovered family basis output) nu chi j := by
  apply adaptiveIpaRootPolynomial_eq_of_chi_before
  exact hchi

/-- The canonical full-assembly polynomial is the straight-line quadratic. -/
private theorem outputIpaPolynomial_canonical_step {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (nu : Fin 11 → Fp) (chi : Fin (AdaptiveActionStatementShape pp).k → Fp) :
    adaptiveIpaRootPolynomial (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        (adaptiveIpaCanonicalProof output.proofData.algebraicProof.erase)
        output.proofData.adaptiveIpaCoordinates
        (outputIpaAssemblyCovered family basis output) nu chi j =
      output.toAlgebraicWfProof.straightLineIpaRootPolynomial nu chi j :=
  output.proofData.adaptiveIpaCanonicalRootPolynomial_eq nu chi j

/-- The final-output IPA surface is its straight-line quadratic whenever the supplied round
record agrees below the current round. -/
theorem outputIpaSurface_eq_straightLine {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (nu : Fin 11 → Fp)
    (chi' chi : Fin (AdaptiveActionStatementShape pp).k → Fp)
    (hchi : ∀ i, i.val < j.val → chi' i = chi i) :
    outputIpaSurface family basis j output nu chi' =
      szBadSet (output.toAlgebraicWfProof.straightLineIpaRootPolynomial nu chi j) := by
  have hcover := output.proofData.adaptiveIpaCanonicalCovered j
  unfold outputIpaSurface
  dsimp only
  rw [dif_pos hcover]
  exact congrArg (fun polynomial : CPoly => (szBadSet polynomial : Set Fp))
    ((outputIpaPolynomial_prefix_step family basis j output nu chi' hcover).trans
      ((outputIpaPolynomial_chi_step family basis j output nu chi' chi hchi).trans
        (outputIpaPolynomial_canonical_step family basis j output nu chi)))

/-- At the selected statement's actual round point, the fallback is exactly the
straight-line IPA quadratic root set. -/
theorem outputIpaFallbackBad_actual {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k) :
    outputIpaFallbackBad family basis j (family.runOutput basis O)
        (family.ipaPoint basis j (family.runOutput basis O)) O =
      szBadSet ((family.runOutput basis O).toAlgebraicWfProof.straightLineIpaRootPolynomial
        (family.runPreIpaReads basis O) (family.runIpaReads basis O) j) := by
  have hlen : (family.ipaPoint basis j (family.runOutput basis O)).val.length =
      preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
        3 * (j.val + 1) := by
    simpa [ipaPoint, AdaptiveActionStatementOutput.prefixes,
      adaptiveIpaRoundLen, adaptiveStatementInitLength] using
      (algebraicFullPrefixes_length_eq_adaptiveIpaRoundLen
        ((family.runOutput basis O).init (family.vkTranscriptRepr basis))
        (family.runOutput basis O).toAlgebraicWfProof j)
  unfold outputIpaFallbackBad outputIpaBad
  rw [if_pos hlen]
  rw [statementIpaPreRecord_ipaPoint family basis O j]
  exact outputIpaSurface_eq_straightLine family basis j (family.runOutput basis O)
    (family.runPreIpaReads basis O)
    (statementIpaRoundRecord j (family.ipaPoint basis j (family.runOutput basis O)) O)
    (family.runIpaReads basis O)
    (fun i hij => statementIpaRoundRecord_ipaPoint_before family basis O j i hij)

/-- At an actual selected-statement pre-IPA point, the root fallback reads precisely the earlier
verifier challenges. -/
theorem outputRootBad_actual {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11) :
    outputRootBad family basis n (family.runOutput basis O)
        (family.preIpaPoint basis n (family.runOutput basis O)) O =
      outputRootSurface family basis n (family.runOutput basis O)
        (fun i => family.runPreIpaReads basis O
          (i.castLE (le_of_lt n.isLt))) := by
  unfold outputRootBad statementPrefixBad
  have hlen : (family.preIpaPoint basis n (family.runOutput basis O)).val.length =
      preIpaLen (AdaptiveActionStatementShape pp)
        (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) n := by
    simpa [preIpaPoint, AdaptiveActionStatementOutput.prefixesPre,
      adaptiveStatementInitLength] using
      (preIpaSqueezePoints_length_eq
        ((family.runOutput basis O).init (family.vkTranscriptRepr basis))
        (family.runOutput basis O).toAlgebraicWfProof.proof.1
        (family.runOutput basis O).toAlgebraicWfProof.proof.2 n)
  rw [if_pos hlen]
  apply congrArg (outputRootSurface family basis n (family.runOutput basis O))
  funext i
  unfold runPreIpaReads
  rw [statementEarlierPrefix_preIpaPoint]
  simp only [preIpaReadsOfOutput, preIpaReadVectorOfOutput, challengeReadVector_get]
  apply congrArg O
  apply Subtype.ext
  rfl

/-- At an actual selected-statement pre-IPA point, the semantic fallback reads precisely the
earlier verifier challenges. -/
theorem outputSemanticBad_actual {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 5) :
    let n11 : Fin 11 := Fin.castLE (by omega) n
    outputSemanticBad family basis n (family.runOutput basis O)
        (family.preIpaPoint basis n11 (family.runOutput basis O)) O =
      outputSemanticSurface family basis n (family.runOutput basis O)
        (fun i => family.runPreIpaReads basis O
          (i.castLE (le_of_lt n11.isLt))) := by
  simp only
  let n11 : Fin 11 := Fin.castLE (by omega) n
  unfold outputSemanticBad
  have hlen : (family.preIpaPoint basis n11 (family.runOutput basis O)).val.length =
      preIpaLen (AdaptiveActionStatementShape pp)
        (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) n11 := by
    simpa [preIpaPoint, AdaptiveActionStatementOutput.prefixesPre,
      adaptiveStatementInitLength] using
      (preIpaSqueezePoints_length_eq
        ((family.runOutput basis O).init (family.vkTranscriptRepr basis))
        (family.runOutput basis O).toAlgebraicWfProof.proof.1
        (family.runOutput basis O).toAlgebraicWfProof.proof.2 n11)
  rw [if_pos hlen]
  apply congrArg (outputSemanticSurface family basis n (family.runOutput basis O))
  funext i
  unfold runPreIpaReads
  rw [statementEarlierPrefix_preIpaPoint]
  simp only [preIpaReadsOfOutput, preIpaReadVectorOfOutput, challengeReadVector_get]
  apply congrArg O
  apply Subtype.ext
  rfl

/-- The selected statement's `x₁` surface is the normalized decoder set. -/
theorem outputRootSurface_five {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (earlier : Fin 5 → Fp) :
    outputRootSurface family basis 5 output earlier =
      adaptiveX1AllRootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        output.proofData.algebraicProof.erase
        (output.proofData.algebraicProof.preX1AssemblySource
          (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
            family.fixedRepresentations basis))
        output.proofData.adaptivePreX1MembersCovered
        (adaptiveEarlierRecord 5 earlier) := by
  unfold outputRootSurface preIpaRepresentationTarget
  rw [List.append_assoc]
  simp only [AdaptiveActionStatementOutput.toAlgebraicWfProof,
    OnlineMemberProofData.toAlgebraicWfProof_proof_fst]
  exact output.proofData.adaptiveRootSurface_five earlier

/-- The selected statement's `x₂` surface is the normalized decoder set. -/
theorem outputRootSurface_six {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (earlier : Fin 6 → Fp) :
    outputRootSurface family basis 6 output earlier =
      adaptiveX2RootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        output.proofData.algebraicProof.erase
        (output.proofData.algebraicProof.preX1AssemblySource
          (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
            family.fixedRepresentations basis))
        output.proofData.adaptivePreX1MembersCovered
        (adaptiveEarlierRecord 6 earlier) := by
  unfold outputRootSurface preIpaRepresentationTarget
  rw [List.append_assoc]
  simp only [AdaptiveActionStatementOutput.toAlgebraicWfProof,
    OnlineMemberProofData.toAlgebraicWfProof_proof_fst]
  exact output.proofData.adaptiveRootSurface_six earlier

/-- The selected statement's `x₃` surface is the normalized decoder set. -/
theorem outputRootSurface_seven {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (earlier : Fin 7 → Fp) :
    outputRootSurface family basis 7 output earlier =
      adaptiveX3RootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        output.proofData.algebraicProof.erase
        (output.proofData.algebraicProof.preX1AssemblySource
          (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
            family.fixedRepresentations basis))
        [output.proofData.algebraicProof.multiopenQPrime]
        output.proofData.adaptivePreX1MembersCovered
        ⟨output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩
        (adaptiveEarlierRecord 7 earlier) := by
  unfold outputRootSurface preIpaRepresentationTarget
  rw [List.append_assoc]
  simp only [AdaptiveActionStatementOutput.toAlgebraicWfProof,
    OnlineMemberProofData.toAlgebraicWfProof_proof_fst]
  exact output.proofData.adaptiveRootSurface_seven earlier

/-- The selected statement's `x₄` surface is the normalized decoder set. -/
theorem outputRootSurface_eight {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (earlier : Fin 8 → Fp) :
    outputRootSurface family basis 8 output earlier =
      adaptiveX4RootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        output.proofData.algebraicProof.erase
        (output.proofData.algebraicProof.preX1AssemblySource
          (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
            family.fixedRepresentations basis))
        [output.proofData.algebraicProof.multiopenQPrime]
        output.proofData.adaptivePreX1MembersCovered
        ⟨output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩
        (adaptiveEarlierRecord 8 earlier) := by
  unfold outputRootSurface preIpaRepresentationTarget
  rw [List.append_assoc]
  simp only [AdaptiveActionStatementOutput.toAlgebraicWfProof,
    OnlineMemberProofData.toAlgebraicWfProof_proof_fst]
  exact output.proofData.adaptiveRootSurface_eight earlier

/-- The selected statement's `ξ` surface is the normalized decoder set. -/
theorem outputRootSurface_nine {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (earlier : Fin 9 → Fp) :
    outputRootSurface family basis 9 output earlier =
      adaptiveXiRootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        output.proofData.algebraicProof.erase
        (output.proofData.algebraicProof.preX1AssemblySource
          (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
            family.fixedRepresentations basis))
        [output.proofData.algebraicProof.multiopenQPrime]
        [output.proofData.algebraicProof.ipaS]
        output.proofData.adaptivePreX1MembersCovered
        ⟨output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨output.proofData.algebraicProof.ipaS, by simp, rfl⟩
        (adaptiveEarlierRecord 9 earlier) := by
  unfold outputRootSurface preIpaRepresentationTarget
  rw [List.append_assoc]
  simp only [AdaptiveActionStatementOutput.toAlgebraicWfProof,
    OnlineMemberProofData.toAlgebraicWfProof_proof_fst]
  exact output.proofData.adaptiveRootSurface_nine earlier

/-- The selected statement's `z` surface is the normalized decoder set. -/
theorem outputRootSurface_ten {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (earlier : Fin 10 → Fp) :
    outputRootSurface family basis 10 output earlier =
      adaptiveZRootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        output.proofData.algebraicProof.erase
        (output.proofData.algebraicProof.preX1AssemblySource
          (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
            family.fixedRepresentations basis))
        [output.proofData.algebraicProof.multiopenQPrime]
        [output.proofData.algebraicProof.ipaS]
        output.proofData.adaptivePreX1MembersCovered
        ⟨output.proofData.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨output.proofData.algebraicProof.ipaS, by simp, rfl⟩
        (adaptiveEarlierRecord 10 earlier) := by
  unfold outputRootSurface preIpaRepresentationTarget
  rw [List.append_assoc]
  simp only [AdaptiveActionStatementOutput.toAlgebraicWfProof,
    OnlineMemberProofData.toAlgebraicWfProof_proof_fst]
  exact output.proofData.adaptiveRootSurface_ten earlier

end ComputedAdaptiveActionStatementFSFamily

end Zcash.Snark
