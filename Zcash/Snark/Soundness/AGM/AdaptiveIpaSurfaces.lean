import Zcash.Snark.Soundness.AGM.AdaptiveRootCore

/-!
# IPA-round surfaces for arbitrary adaptive online-AGM adversaries

Each round quadratic is rebuilt from its first-query representations: the multiopen assembly,
`S`, and round pairs through that round.
-/

namespace Zcash.Snark

open Classical CompPoly.CPolynomial
open scoped ENNReal

variable {shape : Shape}

local instance vestaInhabitedAdaptiveIpaSurfaces : Inhabited VestaG := ⟨0⟩

/-- Explicit algebraic coordinates sufficient to compute every straight-line IPA quadratic. -/
structure AdaptiveIpaCoordinateData
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) where
  multiopenSource : List (AlgebraicPoint (F := Fp) basis)
  s : AlgebraicPoint (F := Fp) basis
  rounds : Fin shape.k →
    AlgebraicPoint (F := Fp) basis × AlgebraicPoint (F := Fp) basis

@[ext] theorem AdaptiveIpaCoordinateData.ext'
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {left right : AdaptiveIpaCoordinateData basis}
    (hmultiopen : left.multiopenSource = right.multiopenSource)
    (hs : left.s = right.s) (hrounds : left.rounds = right.rounds) : left = right := by
  cases left
  cases right
  simp_all

/-- A well-formed ordinary proof decoded from one exact IPA-round query point. -/
structure DecodedIpaPrefix
    (init : List (TranscriptElt Fp VestaG)) (j : Fin shape.k)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k)) where
  proof : WfProof shape
  point_eq : fullPrefixes init proof j = t

/-- Choose a valid IPA-prefix decode at a deployed squeeze point, or `none`. This noncomputable
choice only defines a probability surface; relation extraction remains executable. -/
noncomputable def decodeIpaPrefix?
    (init : List (TranscriptElt Fp VestaG)) (j : Fin shape.k)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k)) :
    Option (DecodedIpaPrefix (shape := shape) init j t) :=
  if h : Nonempty (DecodedIpaPrefix (shape := shape) init j t) then
    some (Classical.choice h)
  else none

theorem decodeIpaPrefix?_isSome
    (init : List (TranscriptElt Fp VestaG)) (j : Fin shape.k)
    (p : WfProof shape) :
    (decodeIpaPrefix? (shape := shape) init j (fullPrefixes init p j)).isSome := by
  have h : Nonempty (DecodedIpaPrefix (shape := shape) init j
      (fullPrefixes init p j)) := ⟨⟨p, rfl⟩⟩
  rw [decodeIpaPrefix?, dif_pos h]
  rfl

/-- Equality of a round-`j` query fixes every prover round pair already absorbed through `j`. -/
theorem ipaRound_eq_of_fullPrefix_eq
    (init : List (TranscriptElt Fp VestaG)) (p q : WfProof shape)
    (j i : Fin shape.k) (hij : i.val ≤ j.val)
    (hpoint : fullPrefixes init p j = fullPrefixes init q j) :
    p.1.ipaRounds i = q.1.ipaRounds i := by
  have hpre := preIpaTranscript_eq_of_fullPrefix_eq init p q j hpoint
  have hpointVal := congrArg Subtype.val hpoint
  change roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j =
    roundTranscriptFin (preIpaTranscript init q.1) q.1.ipaRounds j at hpointVal
  rw [hpre] at hpointVal
  have hiTranscript :
      roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds i =
        roundTranscriptFin (preIpaTranscript init q.1) q.1.ipaRounds i := by
    rw [← roundTranscriptFin_take (preIpaTranscript init p.1) p.1.ipaRounds hij,
      ← roundTranscriptFin_take (preIpaTranscript init q.1) q.1.ipaRounds hij,
      hpre, hpointVal]
  have hiPoint : fullPrefixes init p i = fullPrefixes init q i := by
    apply Subtype.ext
    exact hiTranscript
  calc
    p.1.ipaRounds i = grindDecode (fullPrefixes init p i) := by
      symm
      exact grindDecode_round (preIpaTranscript init p.1) p.1.ipaRounds i _
    _ = grindDecode (fullPrefixes init q i) := congrArg grindDecode hiPoint
    _ = q.1.ipaRounds i :=
      grindDecode_round (preIpaTranscript init q.1) q.1.ipaRounds i _

/-- The zero representation used only for rounds strictly after the priced query. -/
def adaptiveZeroAlgebraicPoint
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    AlgebraicPoint (F := Fp) basis where
  point := 0
  repr :=
    { coeffs := 0
      hEq := by simp [representationEval] }

/-- Keep exactly the algebraic round coordinates visible at the round-`j` query. -/
def AdaptiveIpaCoordinateData.prefix
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (coordinates : AdaptiveIpaCoordinateData basis) : AdaptiveIpaCoordinateData basis where
  multiopenSource := coordinates.multiopenSource
  s := coordinates.s
  rounds := fun i =>
    if i.val ≤ j.val then coordinates.rounds i
    else (adaptiveZeroAlgebraicPoint basis, adaptiveZeroAlgebraicPoint basis)

theorem ProofString.preX1CommitmentPoints_mem_beforeRound
    (ps : ProofString shape Fp VestaG) (j : Fin shape.k) (P : VestaG)
    (hP : P ∈ ps.preX1CommitmentPoints) :
    P ∈ ps.commitmentPointsBeforeRound j := by
  rw [ProofString.commitmentPointsBeforeRound]
  apply List.mem_append_left
  unfold ProofString.commitmentPointsBefore
  simp [hP]

theorem ProofString.multiopenQPrime_mem_beforeRound
    (ps : ProofString shape Fp VestaG) (j : Fin shape.k) :
    ps.multiopenQPrime ∈ ps.commitmentPointsBeforeRound j := by
  rw [ProofString.commitmentPointsBeforeRound]
  apply List.mem_append_left
  simp [ProofString.commitmentPointsBefore]

theorem ProofString.ipaS_mem_beforeRound
    (ps : ProofString shape Fp VestaG) (j : Fin shape.k) :
    ps.ipaS ∈ ps.commitmentPointsBeforeRound j := by
  rw [ProofString.commitmentPointsBeforeRound]
  apply List.mem_append_left
  simp [ProofString.commitmentPointsBefore]

theorem ProofString.ipaRound_mem_beforeRound
    (ps : ProofString shape Fp VestaG) (j i : Fin shape.k) (hij : i.val ≤ j.val) :
    (ps.ipaRounds i).1 ∈ ps.commitmentPointsBeforeRound j ∧
      (ps.ipaRounds i).2 ∈ ps.commitmentPointsBeforeRound j := by
  rw [ProofString.commitmentPointsBeforeRound]
  constructor <;> apply List.mem_append_right
  · apply List.mem_flatMap.mpr
    refine ⟨i, ?_, by simp⟩
    apply List.mem_take_iff_getElem.mpr
    exact ⟨i.val, by simp; omega, by simp⟩
  · apply List.mem_flatMap.mpr
    refine ⟨i, ?_, by simp⟩
    apply List.mem_take_iff_getElem.mpr
    exact ⟨i.val, by simp; omega, by simp⟩

theorem AlgebraicProofString.ipaRound_mem_representationsBeforeRound
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (j i : Fin shape.k) (hij : i.val ≤ j.val) :
    (aps.ipaRounds i).1 ∈ aps.representationsBeforeRound j ∧
      (aps.ipaRounds i).2 ∈ aps.representationsBeforeRound j := by
  rw [AlgebraicProofString.representationsBeforeRound]
  constructor <;> apply List.mem_append_right
  · apply List.mem_flatMap.mpr
    refine ⟨i, ?_, by simp⟩
    apply List.mem_take_iff_getElem.mpr
    exact ⟨i.val, by simp; omega, by simp⟩
  · apply List.mem_flatMap.mpr
    refine ⟨i, ?_, by simp⟩
    apply List.mem_take_iff_getElem.mpr
    exact ⟨i.val, by simp; omega, by simp⟩

/-- Recover one query-time representation of a decoded round-prefix point. -/
def adaptiveIpaQueryRepresentation
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    {t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k)}
    (decoded : DecodedIpaPrefix (shape := shape) init j t)
    (query : AlgebraicTranscriptQuery (F := Fp) basis t)
    (P : VestaG) (hP : P ∈ decoded.proof.1.commitmentPointsBeforeRound j) :
    AlgebraicPoint (F := Fp) basis :=
  query.representationOfPoint P (by
    rw [← decoded.point_eq]
    exact decoded.proof.1.commitmentPointsBeforeRound_covered init decoded.proof.2 j P hP)

/-- A pinned first annotation selects every sublist of the final represented coordinates
literally, not merely pointwise. -/
theorem SelectedQueryRepresentationPinned.representationsFor_eq_self_of_subset
    {α : Type*} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {L : Nat} {t : BTranscript Fp VestaG L}
    {A : LabeledOracleComp (BTranscript Fp VestaG L) Fp
      (AlgebraicTranscriptQuery (F := Fp) basis) α}
    {O : BTranscript Fp VestaG L → Fp}
    {final subset : List (AlgebraicPoint (F := Fp) basis)}
    (pinned : SelectedQueryRepresentationPinned t A O final)
    (hsubset : ∀ ap ∈ subset, ap ∈ final) :
    pinned.query.representationsFor subset (fun ap hap => pinned.covered ap (hsubset ap hap)) =
      subset := by
  have hselected : pinned.query.representationsFor final pinned.covered = final :=
    algebraicPointList_eq_of_maps_eq
      (pinned.query.representationsFor_points final pinned.covered)
      pinned.coefficients_eq
  induction subset with
  | nil => rfl
  | cons ap rest ih =>
      simp only [AlgebraicTranscriptQuery.representationsFor]
      have hap : ap ∈ final := hsubset ap (by simp)
      rw [pinned.query.representationOfPoint_eq_of_representationsFor_eq
        final pinned.covered hselected ap hap]
      congr 1
      exact ih (fun candidate hmem => hsubset candidate (by simp [hmem]))

/-- Deterministic point selection is insensitive to the proof terms establishing coverage. -/
theorem AlgebraicTranscriptQuery.representationsForPoints_congr
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG} {L : Nat}
    {t : BTranscript Fp VestaG L}
    (query : AlgebraicTranscriptQuery (F := Fp) basis t)
    (points points' : List VestaG)
    (hcovered : ∀ P ∈ points, P ∈ transcriptGroupPoints t.val)
    (hcovered' : ∀ P ∈ points', P ∈ transcriptGroupPoints t.val)
    (hpoints : points = points') :
    query.representationsForPoints points hcovered =
      query.representationsForPoints points' hcovered' := by
  subst points'
  rfl

theorem AlgebraicTranscriptQuery.representationOfPoint_congr
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG} {L : Nat}
    {t : BTranscript Fp VestaG L}
    (query : AlgebraicTranscriptQuery (F := Fp) basis t)
    (P Q : VestaG) (hP : P ∈ transcriptGroupPoints t.val)
    (hQ : Q ∈ transcriptGroupPoints t.val) (hpoint : P = Q) :
    query.representationOfPoint P hP = query.representationOfPoint Q hQ := by
  subst Q
  rfl

/-- Explicit coordinates fixed by the first annotation of a decoded round query. -/
def adaptiveIpaQueryCoordinates
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    {t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k)}
    (decoded : DecodedIpaPrefix (shape := shape) init j t)
    (query : AlgebraicTranscriptQuery (F := Fp) basis t)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) :
    AdaptiveIpaCoordinateData basis where
  multiopenSource :=
    query.representationsForPoints decoded.proof.1.preX1CommitmentPoints (by
      intro P hP
      rw [← decoded.point_eq]
      exact decoded.proof.1.commitmentPointsBeforeRound_covered init decoded.proof.2 j P
        (decoded.proof.1.preX1CommitmentPoints_mem_beforeRound j P hP)) ++
      fixed ++
      [adaptiveIpaQueryRepresentation init basis j decoded query
        decoded.proof.1.multiopenQPrime
        (decoded.proof.1.multiopenQPrime_mem_beforeRound j)]
  s := adaptiveIpaQueryRepresentation init basis j decoded query decoded.proof.1.ipaS
    (decoded.proof.1.ipaS_mem_beforeRound j)
  rounds := fun i =>
    if hij : i.val ≤ j.val then
      (adaptiveIpaQueryRepresentation init basis j decoded query
          (decoded.proof.1.ipaRounds i).1
          (decoded.proof.1.ipaRound_mem_beforeRound j i hij).1,
        adaptiveIpaQueryRepresentation init basis j decoded query
          (decoded.proof.1.ipaRounds i).2
          (decoded.proof.1.ipaRound_mem_beforeRound j i hij).2)
    else (adaptiveZeroAlgebraicPoint basis, adaptiveZeroAlgebraicPoint basis)

/-- The initial discrepancy expressed directly through an explicit canonical multiopen source. -/
def adaptiveIpaInitialDiscrepancy
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (coordinates : AdaptiveIpaCoordinateData basis)
    (hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2)
    (nu : Fin 11 → Fp) : Fp :=
  let represented := RepresentedMultiopen.ofCoveredList vk instanceCommitment ps nu
    coordinates.multiopenSource (hcover nu)
  let msm := multiopenMsm vk instanceCommitment ps (chRecord nu (fun _ => 0))
  let aMulti := msm.gScalars + repsGPart represented.reps
  let multiU := msm.uScalar + repsU represented.reps
  nu 10 * (innerProduct aMulti (evalVector shape.k (nu 7)) -
      multiopenValue vk instanceCommitment ps (chRecord nu (fun _ => 0)) +
      nu 9 * innerProduct coordinates.s.gPart (evalVector shape.k (nu 7))) -
    (multiU + nu 9 * coordinates.s.coeffs AugmentedIndex.u)

/-- Replacing only the IPA suffix leaves the pre-IPA assembly MSM unchanged. -/
theorem multiopenMsm_spliceIpa
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (rounds : Fin shape.k → VestaG × VestaG) (c f : Fp)
    (ch : Challenges shape.k Fp) :
    multiopenMsm vk instanceCommitment (spliceIpa ps rounds c f) ch =
      multiopenMsm vk instanceCommitment ps ch := by
  rfl

/-- Rebuilding representations from the same covering source is unchanged by a suffix splice. -/
theorem representedMultiopenOfCoveredList_spliceIpa_reps
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (rounds : Fin shape.k → VestaG × VestaG) (c f : Fp)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).other → ∃ ap ∈ source, ap.point = pr.2)
    (hcover' : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment (spliceIpa ps rounds c f)
        (chRecord nu (fun _ => 0))).other → ∃ ap ∈ source, ap.point = pr.2)
    (nu : Fin 11 → Fp) :
    (RepresentedMultiopen.ofCoveredList vk instanceCommitment (spliceIpa ps rounds c f)
        nu source (hcover' nu)).reps =
      (RepresentedMultiopen.ofCoveredList vk instanceCommitment ps
        nu source (hcover nu)).reps := by
  unfold RepresentedMultiopen.ofCoveredList
  simp only [multiopenMsm_spliceIpa]

/-- The explicit initial discrepancy likewise ignores the replaced IPA suffix. -/
theorem adaptiveIpaInitialDiscrepancy_spliceIpa
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (rounds : Fin shape.k → VestaG × VestaG) (c f : Fp)
    (coordinates : AdaptiveIpaCoordinateData basis)
    (hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2)
    (hcover' : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment (spliceIpa ps rounds c f)
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2)
    (nu : Fin 11 → Fp) :
    adaptiveIpaInitialDiscrepancy vk instanceCommitment (spliceIpa ps rounds c f)
        coordinates hcover' nu =
      adaptiveIpaInitialDiscrepancy vk instanceCommitment ps coordinates hcover nu := by
  have hreps := representedMultiopenOfCoveredList_spliceIpa_reps
    vk instanceCommitment ps rounds c f coordinates.multiopenSource hcover hcover' nu
  unfold adaptiveIpaInitialDiscrepancy
  simp only [multiopenMsm_spliceIpa, multiopenValue_spliceIpa]
  rw [hreps]

/-- The quadratic fixed before one IPA squeeze, computed only from explicit prefix coordinates. -/
def adaptiveIpaRootPolynomial
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (coordinates : AdaptiveIpaCoordinateData basis)
    (hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2)
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp) (j : Fin shape.k) :
    CPoly :=
  ipaDiscrepancyPolynomialAt
    (adaptiveIpaInitialDiscrepancy vk instanceCommitment ps coordinates hcover nu)
    ((List.ofFn coordinates.rounds).map
      (representedRoundDiscrepancy (evalVector shape.k (nu 7)) (nu 10)))
    (List.ofFn chi) j.val

/-- The round polynomial depends on the explicit coordinates, not on replaced proof-suffix
fields. -/
theorem adaptiveIpaRootPolynomial_spliceIpa
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (rounds : Fin shape.k → VestaG × VestaG) (c f : Fp)
    (coordinates : AdaptiveIpaCoordinateData basis)
    (hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2)
    (hcover' : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment (spliceIpa ps rounds c f)
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2)
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp) (j : Fin shape.k) :
    adaptiveIpaRootPolynomial vk instanceCommitment (spliceIpa ps rounds c f)
        coordinates hcover' nu chi j =
      adaptiveIpaRootPolynomial vk instanceCommitment ps coordinates hcover nu chi j := by
  unfold adaptiveIpaRootPolynomial
  rw [adaptiveIpaInitialDiscrepancy_spliceIpa]

/-- The discrepancy polynomial at index `j` reads only the first `j+1` round entries. -/
theorem ipaDiscrepancyPolynomialAt_eq_of_rounds_take_eq
    (initial : Fp) (rounds rounds' : List (Fp × Fp)) (challenges : List Fp) (j : Nat)
    (hrounds : rounds.take (j + 1) = rounds'.take (j + 1)) :
    ipaDiscrepancyPolynomialAt initial rounds challenges j =
      ipaDiscrepancyPolynomialAt initial rounds' challenges j := by
  induction j generalizing initial rounds rounds' challenges with
  | zero =>
      cases rounds with
      | nil =>
          cases rounds' <;> simp_all [ipaDiscrepancyPolynomialAt]
      | cons round rounds =>
          cases rounds' with
          | nil => simp_all
          | cons round' rounds' =>
              have hhead : round = round' := by simpa using hrounds
              subst round'
              cases challenges <;> rfl
  | succ j ih =>
      cases rounds with
      | nil =>
          cases rounds' <;> simp_all [ipaDiscrepancyPolynomialAt]
      | cons round rounds =>
          cases rounds' with
          | nil => simp_all
          | cons round' rounds' =>
              have hparts : round = round' ∧
                  rounds.take (j + 1) = rounds'.take (j + 1) := by
                simpa only [List.take_succ_cons, List.cons.injEq] using hrounds
              rcases hparts with ⟨rfl, htail⟩
              cases challenges with
              | nil => rfl
              | cons challenge challenges =>
                  exact ih (ipaDiscrepancyStep initial round challenge) rounds rounds'
                    challenges htail

/-- The polynomial fixed before round `j` reads only challenges strictly before `j`. -/
theorem ipaDiscrepancyPolynomialAt_eq_of_challenges_take_eq
    (initial : Fp) (rounds : List (Fp × Fp)) (challenges challenges' : List Fp) (j : Nat)
    (hlength : challenges.length = challenges'.length)
    (hchallenges : challenges.take j = challenges'.take j) :
    ipaDiscrepancyPolynomialAt initial rounds challenges j =
      ipaDiscrepancyPolynomialAt initial rounds challenges' j := by
  induction j generalizing initial rounds challenges challenges' with
  | zero =>
      cases rounds <;> cases challenges <;> cases challenges' <;>
        simp_all [ipaDiscrepancyPolynomialAt]
  | succ j ih =>
      cases rounds with
      | nil => rfl
      | cons round rounds =>
          cases challenges with
          | nil =>
              cases challenges' with
              | nil => rfl
              | cons challenge' challenges' => simp at hlength
          | cons challenge challenges =>
              cases challenges' with
              | nil => simp at hlength
              | cons challenge' challenges' =>
                  have hparts : challenge = challenge' ∧
                      challenges.take j = challenges'.take j := by
                    simpa only [List.take_succ_cons, List.cons.injEq] using hchallenges
                  rcases hparts with ⟨hhead, htail⟩
                  subst challenge'
                  exact ih (ipaDiscrepancyStep initial round challenge) rounds
                    challenges challenges' (by simpa using hlength) htail

/-- Pointwise agreement before `j` is enough to identify the round-`j` quadratic. -/
theorem adaptiveIpaRootPolynomial_eq_of_chi_before
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (coordinates : AdaptiveIpaCoordinateData basis)
    (hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2)
    (nu : Fin 11 → Fp) (chi chi' : Fin shape.k → Fp) (j : Fin shape.k)
    (hchi : ∀ i : Fin shape.k, i.val < j.val → chi i = chi' i) :
    adaptiveIpaRootPolynomial vk instanceCommitment ps coordinates hcover nu chi j =
      adaptiveIpaRootPolynomial vk instanceCommitment ps coordinates hcover nu chi' j := by
  unfold adaptiveIpaRootPolynomial
  apply ipaDiscrepancyPolynomialAt_eq_of_challenges_take_eq
  · simp
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_take, List.getElem_ofFn]
    have hij : i < j.val := by simpa using hi'
    exact hchi ⟨i, lt_trans hij j.isLt⟩ (by simpa using hi)

/-- Zeroing coordinates emitted strictly after round `j` leaves its root polynomial unchanged. -/
theorem adaptiveIpaRootPolynomial_prefix
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (coordinates : AdaptiveIpaCoordinateData basis)
    (hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2)
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp) (j : Fin shape.k) :
    adaptiveIpaRootPolynomial vk instanceCommitment ps
        (coordinates.prefix basis j) (by simpa [AdaptiveIpaCoordinateData.prefix] using hcover)
        nu chi j =
      adaptiveIpaRootPolynomial vk instanceCommitment ps coordinates hcover nu chi j := by
  unfold adaptiveIpaRootPolynomial AdaptiveIpaCoordinateData.prefix
  apply ipaDiscrepancyPolynomialAt_eq_of_rounds_take_eq
  rw [← List.map_take, ← List.map_take]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hij : i ≤ j.val := by
      simp only [List.length_take, List.length_ofFn] at hi
      omega
    simp
    intro hji
    have hji' : j.val < i := hji
    omega

/-- Every explicit round-local surface remains quadratic. -/
theorem adaptiveIpaRootPolynomial_measure_le
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (coordinates : AdaptiveIpaCoordinateData basis)
    (hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2)
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp) (j : Fin shape.k) :
    uniformChallenge.toOuterMeasure
        (szBadSet (adaptiveIpaRootPolynomial vk instanceCommitment ps coordinates
          hcover nu chi j)) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  refine le_trans (uniformChallenge_szBadSet _) (ENNReal.div_le_div_right ?_ _)
  exact_mod_cast ipaDiscrepancyPolynomialAt_natDegree_le
    (adaptiveIpaInitialDiscrepancy vk instanceCommitment ps coordinates hcover nu)
    ((List.ofFn coordinates.rounds).map
      (representedRoundDiscrepancy (evalVector shape.k (nu 7)) (nu 10)))
    (List.ofFn chi) j.val

/-- Final online proof data, viewed through the explicit coordinate interface. -/
def OnlineMemberProofData.adaptiveIpaCoordinates
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) : AdaptiveIpaCoordinateData basis where
  multiopenSource := data.algebraicProof.multiopenAssemblySource fixed
  s := data.algebraicProof.ipaS
  rounds := data.algebraicProof.ipaRounds

/-- If the round provenance finder returned no relation, coordinates decoded from the first
actual query annotation are exactly the final coordinates visible through that query. -/
theorem adaptiveIpaQueryCoordinates_eq_of_pinned
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (j : Fin shape.k)
    (decoded : DecodedIpaPrefix (shape := shape) family.init j
      (algebraicFullPrefixes family.init
        ((family.adversary basis).run O).toAlgebraicWfProof j))
    (pinned : SelectedQueryRepresentationPinned
      (algebraicFullPrefixes family.init
        ((family.adversary basis).run O).toAlgebraicWfProof j)
      (family.adversary basis) O
      (((family.adversary basis).run O).algebraicProof.representationsBeforeRound j)) :
    adaptiveIpaQueryCoordinates family.init basis j decoded pinned.query
        (family.fixedRepresentations basis) =
      (((family.adversary basis).run O).adaptiveIpaCoordinates.prefix basis j) := by
  let data := (family.adversary basis).run O
  let final := data.algebraicProof.representationsBeforeRound j
  have hpre := preIpaTranscript_eq_of_fullPrefix_eq family.init decoded.proof
    data.toAlgebraicWfProof.proof j decoded.point_eq
  have hsplice : decoded.proof.1 = spliceIpa data.algebraicProof.erase
      decoded.proof.1.ipaRounds decoded.proof.1.ipaC decoded.proof.1.ipaF :=
    preIpaTranscript_inj family.init decoded.proof.2 data.wellFormed hpre
  have hselected : pinned.query.representationsFor final pinned.covered = final :=
    algebraicPointList_eq_of_maps_eq
      (pinned.query.representationsFor_points final pinned.covered)
      pinned.coefficients_eq
  have hpreSubset : ∀ ap ∈ data.algebraicProof.preX1Points, ap ∈ final := by
    intro ap hap
    apply List.mem_append_left
    exact data.algebraicProof.preX1Points_mem_representationsBefore 10 ap hap
  have hqSubset : data.algebraicProof.multiopenQPrime ∈ final := by
    apply List.mem_append_left
    exact data.algebraicProof.multiopenQPrime_mem_representationsBefore 10 (by omega)
  have hsSubset : data.algebraicProof.ipaS ∈ final := by
    apply List.mem_append_left
    exact data.algebraicProof.ipaS_mem_representationsBefore 10 (by omega)
  have hprePoints : decoded.proof.1.preX1CommitmentPoints =
      data.algebraicProof.preX1Points.map AlgebraicPoint.point := by
    calc
      decoded.proof.1.preX1CommitmentPoints =
          data.algebraicProof.erase.preX1CommitmentPoints := by rw [hsplice]; rfl
      _ = data.algebraicProof.preX1Points.map AlgebraicPoint.point := by
        have hp := data.algebraicProof.representationsBefore_points (5 : Fin 11)
        simpa [AlgebraicProofString.representationsBefore,
          ProofString.commitmentPointsBefore] using hp.symm
  have hpreSelected : pinned.query.representationsForPoints
      decoded.proof.1.preX1CommitmentPoints (by
        intro P hP
        rw [← decoded.point_eq]
        exact decoded.proof.1.commitmentPointsBeforeRound_covered family.init
          decoded.proof.2 j P
          (decoded.proof.1.preX1CommitmentPoints_mem_beforeRound j P hP)) =
      data.algebraicProof.preX1Points := by
    let decodedCovered : ∀ P ∈ decoded.proof.1.preX1CommitmentPoints,
        P ∈ transcriptGroupPoints
          (algebraicFullPrefixes family.init data.toAlgebraicWfProof j).val := by
      intro P hP
      rw [← decoded.point_eq]
      exact decoded.proof.1.commitmentPointsBeforeRound_covered family.init
        decoded.proof.2 j P
        (decoded.proof.1.preX1CommitmentPoints_mem_beforeRound j P hP)
    let finalCovered : ∀ P ∈ data.algebraicProof.preX1Points.map AlgebraicPoint.point,
        P ∈ transcriptGroupPoints
          (algebraicFullPrefixes family.init data.toAlgebraicWfProof j).val := by
      intro P hP
      obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hP
      exact pinned.covered ap (hpreSubset ap hap)
    have hqueryPoints : pinned.query.representationsForPoints
        decoded.proof.1.preX1CommitmentPoints decodedCovered =
        pinned.query.representationsForPoints
          (data.algebraicProof.preX1Points.map AlgebraicPoint.point) finalCovered := by
      exact pinned.query.representationsForPoints_congr _ _ decodedCovered finalCovered hprePoints
    rw [hqueryPoints,
      ← pinned.query.representationsFor_eq_representationsForPoints
        data.algebraicProof.preX1Points]
    exact pinned.representationsFor_eq_self_of_subset hpreSubset
  have hqPoint : decoded.proof.1.multiopenQPrime =
      data.algebraicProof.multiopenQPrime.point := by rw [hsplice]; rfl
  have hsPoint : decoded.proof.1.ipaS = data.algebraicProof.ipaS.point := by
    rw [hsplice]
    rfl
  have hqSelected : adaptiveIpaQueryRepresentation family.init basis j decoded pinned.query
      decoded.proof.1.multiopenQPrime
        (decoded.proof.1.multiopenQPrime_mem_beforeRound j) =
      data.algebraicProof.multiopenQPrime := by
    unfold adaptiveIpaQueryRepresentation
    have htarget := pinned.query.representationOfPoint_eq_of_representationsFor_eq
      final pinned.covered hselected data.algebraicProof.multiopenQPrime hqSubset
    exact (pinned.query.representationOfPoint_congr _ _ _ _ hqPoint).trans htarget
  have hsSelected : adaptiveIpaQueryRepresentation family.init basis j decoded pinned.query
      decoded.proof.1.ipaS (decoded.proof.1.ipaS_mem_beforeRound j) =
      data.algebraicProof.ipaS := by
    unfold adaptiveIpaQueryRepresentation
    have htarget := pinned.query.representationOfPoint_eq_of_representationsFor_eq
      final pinned.covered hselected data.algebraicProof.ipaS hsSubset
    exact (pinned.query.representationOfPoint_congr _ _ _ _ hsPoint).trans htarget
  apply AdaptiveIpaCoordinateData.ext'
  · change pinned.query.representationsForPoints
        decoded.proof.1.preX1CommitmentPoints _ ++ family.fixedRepresentations basis ++
          [adaptiveIpaQueryRepresentation family.init basis j decoded pinned.query
            decoded.proof.1.multiopenQPrime
              (decoded.proof.1.multiopenQPrime_mem_beforeRound j)] =
        (data.algebraicProof.preX1Points ++ family.fixedRepresentations basis) ++
          [data.algebraicProof.multiopenQPrime]
    rw [hpreSelected, hqSelected]
  · change adaptiveIpaQueryRepresentation family.init basis j decoded pinned.query
        decoded.proof.1.ipaS (decoded.proof.1.ipaS_mem_beforeRound j) =
      data.algebraicProof.ipaS
    exact hsSelected
  · funext i
    by_cases hij : i.val ≤ j.val
    · have hroundPoint := ipaRound_eq_of_fullPrefix_eq family.init decoded.proof
        data.toAlgebraicWfProof.proof j i hij decoded.point_eq
      have hroundSubset := data.algebraicProof.ipaRound_mem_representationsBeforeRound j i hij
      have hL : adaptiveIpaQueryRepresentation family.init basis j decoded pinned.query
          (decoded.proof.1.ipaRounds i).1
            (decoded.proof.1.ipaRound_mem_beforeRound j i hij).1 =
          (data.algebraicProof.ipaRounds i).1 := by
        unfold adaptiveIpaQueryRepresentation
        have htarget := pinned.query.representationOfPoint_eq_of_representationsFor_eq
          final pinned.covered hselected (data.algebraicProof.ipaRounds i).1 hroundSubset.1
        exact (pinned.query.representationOfPoint_congr _ _ _ _
          (congrArg Prod.fst hroundPoint)).trans htarget
      have hR : adaptiveIpaQueryRepresentation family.init basis j decoded pinned.query
          (decoded.proof.1.ipaRounds i).2
            (decoded.proof.1.ipaRound_mem_beforeRound j i hij).2 =
          (data.algebraicProof.ipaRounds i).2 := by
        unfold adaptiveIpaQueryRepresentation
        have htarget := pinned.query.representationOfPoint_eq_of_representationsFor_eq
          final pinned.covered hselected (data.algebraicProof.ipaRounds i).2 hroundSubset.2
        exact (pinned.query.representationOfPoint_congr _ _ _ _
          (congrArg Prod.snd hroundPoint)).trans htarget
      have hijFin : i ≤ j := hij
      simp [adaptiveIpaQueryCoordinates, OnlineMemberProofData.adaptiveIpaCoordinates,
        AdaptiveIpaCoordinateData.prefix, hijFin, hL, hR, data]
    · have hijFin : ¬ i ≤ j := by
        intro h
        exact hij h
      simp [adaptiveIpaQueryCoordinates, OnlineMemberProofData.adaptiveIpaCoordinates,
        AdaptiveIpaCoordinateData.prefix, hijFin]

/-! ## Blind round-local bad sets -/

def adaptiveIpaRoundLen (init : List (TranscriptElt Fp VestaG)) (j : Fin shape.k) : Nat :=
  preIpaLen shape init.length 10 + 3 * (j.val + 1)

def adaptiveEarlierRoundPrefix
    (init : List (TranscriptElt Fp VestaG)) {L : Nat}
    (t : BTranscript Fp VestaG L) (i : Fin shape.k) : BTranscript Fp VestaG L :=
  ⟨t.val.take (adaptiveIpaRoundLen (shape := shape) init i), by
    rw [List.length_take]
    exact le_trans (min_le_right _ _) t.prop⟩

theorem adaptiveIpaPrePrefix_ne
    (init : List (TranscriptElt Fp VestaG)) {L : Nat}
    (j : Fin shape.k) (t : BTranscript Fp VestaG L)
    (hlen : t.val.length = adaptiveIpaRoundLen (shape := shape) init j)
    (n : Fin 11) :
    adaptiveEarlierPrefix (shape := shape) init t n ≠ t := by
  intro heq
  have hlens := congrArg (fun q : BTranscript Fp VestaG L => q.val.length) heq
  simp only [adaptiveEarlierPrefix, List.length_take] at hlens
  have hlt : preIpaLen shape init.length n < t.val.length := by
    rw [hlen]
    fin_cases n <;> simp [adaptiveIpaRoundLen, preIpaLen] <;> omega
  rw [min_eq_left hlt.le] at hlens
  omega

theorem adaptiveEarlierRoundPrefix_ne
    (init : List (TranscriptElt Fp VestaG)) {L : Nat}
    (j : Fin shape.k) (t : BTranscript Fp VestaG L)
    (hlen : t.val.length = adaptiveIpaRoundLen (shape := shape) init j)
    (i : Fin shape.k) (hij : i.val < j.val) :
    adaptiveEarlierRoundPrefix (shape := shape) init t i ≠ t := by
  intro heq
  have hlens := congrArg (fun q : BTranscript Fp VestaG L => q.val.length) heq
  simp only [adaptiveEarlierRoundPrefix, List.length_take] at hlens
  have hlt : adaptiveIpaRoundLen (shape := shape) init i < t.val.length := by
    rw [hlen]
    simp only [adaptiveIpaRoundLen]
    omega
  rw [min_eq_left hlt.le] at hlens
  omega

def adaptiveIpaPreRecord
    (init : List (TranscriptElt Fp VestaG)) {L : Nat}
    (t : BTranscript Fp VestaG L) (O : BTranscript Fp VestaG L → Fp) : Fin 11 → Fp :=
  fun n => O (adaptiveEarlierPrefix (shape := shape) init t n)

def adaptiveIpaRoundRecord
    (init : List (TranscriptElt Fp VestaG)) {L : Nat}
    (j : Fin shape.k) (t : BTranscript Fp VestaG L)
    (O : BTranscript Fp VestaG L → Fp) : Fin shape.k → Fp :=
  fun i => if _h : i.val < j.val then
    O (adaptiveEarlierRoundPrefix (shape := shape) init t i)
  else 0

theorem adaptiveIpaPreRecord_update_self
    (init : List (TranscriptElt Fp VestaG)) {L : Nat}
    (j : Fin shape.k) (t : BTranscript Fp VestaG L)
    (hlen : t.val.length = adaptiveIpaRoundLen (shape := shape) init j)
    (O : BTranscript Fp VestaG L → Fp) (v : Fp) :
    adaptiveIpaPreRecord (shape := shape) init t (Function.update O t v) =
      adaptiveIpaPreRecord (shape := shape) init t O := by
  funext n
  unfold adaptiveIpaPreRecord
  rw [Function.update_of_ne]
  exact adaptiveIpaPrePrefix_ne init j t hlen n

theorem adaptiveIpaRoundRecord_update_self
    (init : List (TranscriptElt Fp VestaG)) {L : Nat}
    (j : Fin shape.k) (t : BTranscript Fp VestaG L)
    (hlen : t.val.length = adaptiveIpaRoundLen (shape := shape) init j)
    (O : BTranscript Fp VestaG L → Fp) (v : Fp) :
    adaptiveIpaRoundRecord (shape := shape) init j t (Function.update O t v) =
      adaptiveIpaRoundRecord (shape := shape) init j t O := by
  funext i
  unfold adaptiveIpaRoundRecord
  split
  · rw [Function.update_of_ne]
    exact adaptiveEarlierRoundPrefix_ne init j t hlen i (by assumption)
  · rfl

/-- Erase IPA fields that are not part of the ordinary data used by a round quadratic. -/
def adaptiveIpaCanonicalProof (ps : ProofString shape Fp VestaG) :
    ProofString shape Fp VestaG := spliceIpa ps 0 0 0

def adaptiveQueriedIpaSurfaceCore
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp) : Set Fp :=
  if t.val.length = adaptiveIpaRoundLen (shape := shape) family.init j then
    match decodeIpaPrefix? (shape := shape) family.init j t with
    | none => ∅
    | some decoded =>
        let ps := adaptiveIpaCanonicalProof decoded.proof.1
        let coordinates := adaptiveIpaQueryCoordinates family.init basis j decoded label
          (family.fixedRepresentations basis)
        if hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
            pr ∈ (multiopenMsm (family.vk basis) (family.instanceCommitment basis) ps
              (chRecord nu (fun _ => 0))).other →
              ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2 then
          szBadSet (adaptiveIpaRootPolynomial (family.vk basis)
            (family.instanceCommitment basis) ps coordinates hcover
            nu chi j)
        else ∅
  else ∅

def adaptiveFallbackIpaSurfaceCore
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp) : Set Fp :=
  if t.val.length = adaptiveIpaRoundLen (shape := shape) family.init j then
    let ps := adaptiveIpaCanonicalProof data.algebraicProof.erase
    let coordinates := data.adaptiveIpaCoordinates.prefix basis j
    if hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
        pr ∈ (multiopenMsm (family.vk basis) (family.instanceCommitment basis) ps
          (chRecord nu (fun _ => 0))).other →
          ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2 then
      szBadSet (adaptiveIpaRootPolynomial (family.vk basis)
        (family.instanceCommitment basis) ps coordinates hcover
        nu chi j)
    else ∅
  else ∅

def adaptiveQueriedIpaSurface
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) : Set Fp :=
  adaptiveQueriedIpaSurfaceCore family basis j t label
    (adaptiveIpaPreRecord (shape := shape) family.init t O)
    (adaptiveIpaRoundRecord (shape := shape) family.init j t O)

def adaptiveFallbackIpaSurface
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) : Set Fp :=
  adaptiveFallbackIpaSurfaceCore family basis j data t
    (adaptiveIpaPreRecord (shape := shape) family.init t O)
    (adaptiveIpaRoundRecord (shape := shape) family.init j t O)

/-- Irreducible names keep the large dependent bad-set bodies out of theorem unification. -/
@[irreducible] def adaptiveIpaQueriedBad
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k) :=
  adaptiveQueriedIpaSurface family basis j

@[irreducible] def adaptiveIpaFallbackBad
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k) :=
  adaptiveFallbackIpaSurface family basis j

theorem adaptiveQueriedIpaSurfaceCore_measure_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveQueriedIpaSurfaceCore family basis j t label nu chi) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  unfold adaptiveQueriedIpaSurfaceCore
  split
  · split
    · simp
    · dsimp only
      split
      · exact adaptiveIpaRootPolynomial_measure_le _ _ _ _ _ _ _ j
      · simp
  · simp

theorem adaptiveFallbackIpaSurfaceCore_measure_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveFallbackIpaSurfaceCore family basis j data t nu chi) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  unfold adaptiveFallbackIpaSurfaceCore
  split
  · dsimp only
    split
    · exact adaptiveIpaRootPolynomial_measure_le _ _ _ _ _ _ _ j
    · simp
  · simp

theorem adaptiveQueriedIpaSurface_measure_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveQueriedIpaSurface family basis j t label O) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  unfold adaptiveQueriedIpaSurface
  exact adaptiveQueriedIpaSurfaceCore_measure_le _ _ _ _ _ _ _

theorem adaptiveFallbackIpaSurface_measure_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveFallbackIpaSurface family basis j data t O) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  unfold adaptiveFallbackIpaSurface
  exact adaptiveFallbackIpaSurfaceCore_measure_le _ _ _ _ _ _ _

theorem adaptiveIpaRootSet_congr_records
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG) (coordinates : AdaptiveIpaCoordinateData basis)
    (hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2)
    (nu nu' : Fin 11 → Fp) (chi chi' : Fin shape.k → Fp) (j : Fin shape.k)
    (hnu : nu = nu') (hchi : chi = chi') :
    szBadSet (adaptiveIpaRootPolynomial vk instanceCommitment ps coordinates hcover nu chi j) =
      szBadSet (adaptiveIpaRootPolynomial vk instanceCommitment ps coordinates hcover nu' chi' j) := by
  subst nu'
  subst chi'
  rfl

theorem adaptiveQueriedIpaSurface_update_self
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp) :
    adaptiveQueriedIpaSurface family basis j t label (Function.update O t v) =
      adaptiveQueriedIpaSurface family basis j t label O := by
  unfold adaptiveQueriedIpaSurface
  by_cases hlen : t.val.length = adaptiveIpaRoundLen (shape := shape) family.init j
  · rw [adaptiveIpaPreRecord_update_self family.init j t hlen O v,
      adaptiveIpaRoundRecord_update_self family.init j t hlen O v]
  · simp [adaptiveQueriedIpaSurfaceCore, hlen]

theorem adaptiveFallbackIpaSurface_update_self
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp) :
    adaptiveFallbackIpaSurface family basis j data t (Function.update O t v) =
      adaptiveFallbackIpaSurface family basis j data t O := by
  unfold adaptiveFallbackIpaSurface
  by_cases hlen : t.val.length = adaptiveIpaRoundLen (shape := shape) family.init j
  · rw [adaptiveIpaPreRecord_update_self family.init j t hlen O v,
      adaptiveIpaRoundRecord_update_self family.init j t hlen O v]
  · simp [adaptiveFallbackIpaSurfaceCore, hlen]

theorem adaptiveIpaQueriedBad_update_self
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp) :
    adaptiveIpaQueriedBad family basis j t label (Function.update O t v) =
      adaptiveIpaQueriedBad family basis j t label O := by
  unfold adaptiveIpaQueriedBad
  exact adaptiveQueriedIpaSurface_update_self family basis j t label O v

theorem adaptiveIpaFallbackBad_update_self
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp) :
    adaptiveIpaFallbackBad family basis j data t (Function.update O t v) =
      adaptiveIpaFallbackBad family basis j data t O := by
  unfold adaptiveIpaFallbackBad
  exact adaptiveFallbackIpaSurface_update_self family basis j data t O v

theorem adaptiveIpaQueriedBad_measure_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    uniformChallenge.toOuterMeasure (adaptiveIpaQueriedBad family basis j t label O) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  unfold adaptiveIpaQueriedBad
  exact adaptiveQueriedIpaSurface_measure_le family basis j t label O

theorem adaptiveIpaFallbackBad_measure_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    uniformChallenge.toOuterMeasure (adaptiveIpaFallbackBad family basis j data t O) ≤
      2 / (Fintype.card Fp : ENNReal) := by
  unfold adaptiveIpaFallbackBad
  exact adaptiveFallbackIpaSurface_measure_le family basis j data t O

theorem algebraicFullPrefixes_length_eq_adaptiveIpaRoundLen
    (init : List (TranscriptElt Fp VestaG))
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (j : Fin shape.k) :
    (algebraicFullPrefixes init p j).val.length =
      adaptiveIpaRoundLen (shape := shape) init j := by
  change (roundTranscriptFin (preIpaTranscript init p.algebraicProof.erase)
    p.algebraicProof.erase.ipaRounds j).length = _
  rw [roundTranscriptFin_length,
    preIpaTranscript_length_eq init p.algebraicProof.erase p.wellFormed]
  rfl

theorem OnlineMemberProofData.adaptiveIpaCanonicalCovered
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (j : Fin shape.k) :
    ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment
        (adaptiveIpaCanonicalProof data.algebraicProof.erase)
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ (data.adaptiveIpaCoordinates.prefix basis j).multiopenSource,
          ap.point = pr.2 := by
  intro nu pr hpr
  apply data.assemblyCovered nu pr
  exact hpr

theorem adaptiveIpaRootSet_congr_coordinates
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps ps' : ProofString shape Fp VestaG)
    (coordinates coordinates' : AdaptiveIpaCoordinateData basis)
    (hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2)
    (hcover' : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment ps'
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates'.multiopenSource, ap.point = pr.2)
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp) (j : Fin shape.k)
    (hps : ps = ps') (hcoordinates : coordinates = coordinates') :
    szBadSet (adaptiveIpaRootPolynomial vk instanceCommitment ps coordinates
        hcover nu chi j) =
      szBadSet (adaptiveIpaRootPolynomial vk instanceCommitment ps' coordinates'
        hcover' nu chi j) := by
  subst ps'
  subst coordinates'
  rfl

theorem adaptiveIpaSurfaceCore_eq
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (decoded : DecodedIpaPrefix (shape := shape) family.init j t)
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp)
    (hlen : t.val.length = adaptiveIpaRoundLen (shape := shape) family.init j)
    (hdecode : decodeIpaPrefix? (shape := shape) family.init j t = some decoded)
    (hcanonical : adaptiveIpaCanonicalProof decoded.proof.1 =
      adaptiveIpaCanonicalProof data.algebraicProof.erase)
    (hcoordinates : adaptiveIpaQueryCoordinates family.init basis j decoded label
      (family.fixedRepresentations basis) = data.adaptiveIpaCoordinates.prefix basis j)
    (hqueryCover : ∀ rho : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm (family.vk basis) (family.instanceCommitment basis)
        (adaptiveIpaCanonicalProof decoded.proof.1)
        (chRecord rho (fun _ => 0))).other →
        ∃ ap ∈ (adaptiveIpaQueryCoordinates family.init basis j decoded label
          (family.fixedRepresentations basis)).multiopenSource, ap.point = pr.2)
    (hfinalCover : ∀ rho : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm (family.vk basis) (family.instanceCommitment basis)
        (adaptiveIpaCanonicalProof data.algebraicProof.erase)
        (chRecord rho (fun _ => 0))).other →
        ∃ ap ∈ (data.adaptiveIpaCoordinates.prefix basis j).multiopenSource,
          ap.point = pr.2) :
  adaptiveQueriedIpaSurfaceCore family basis j t label nu chi =
      adaptiveFallbackIpaSurfaceCore family basis j data t nu chi := by
  unfold adaptiveQueriedIpaSurfaceCore adaptiveFallbackIpaSurfaceCore
  rw [if_pos hlen, hdecode]
  dsimp only
  rw [dif_pos hqueryCover, if_pos hlen]
  rw [dif_pos hfinalCover]
  exact congrArg (fun s : Finset Fp => (s : Set Fp))
    (adaptiveIpaRootSet_congr_coordinates _ _ _ _ _ _ _ _ _ _ _
      hcanonical hcoordinates)

theorem adaptiveQueriedIpaSurface_eq_fallback_of_pinned
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (j : Fin shape.k)
    (decoded : DecodedIpaPrefix (shape := shape) family.init j
      (algebraicFullPrefixes family.init
        ((family.adversary basis).run O).toAlgebraicWfProof j))
    (hdecode : decodeIpaPrefix? (shape := shape) family.init j
      (algebraicFullPrefixes family.init
        ((family.adversary basis).run O).toAlgebraicWfProof j) = some decoded)
    (pinned : SelectedQueryRepresentationPinned
      (algebraicFullPrefixes family.init
        ((family.adversary basis).run O).toAlgebraicWfProof j)
      (family.adversary basis) O
      (((family.adversary basis).run O).algebraicProof.representationsBeforeRound j)) :
    adaptiveQueriedIpaSurface family basis j
        (algebraicFullPrefixes family.init
          ((family.adversary basis).run O).toAlgebraicWfProof j)
        pinned.query O =
      adaptiveFallbackIpaSurface family basis j ((family.adversary basis).run O)
        (algebraicFullPrefixes family.init
          ((family.adversary basis).run O).toAlgebraicWfProof j) O := by
  let data := (family.adversary basis).run O
  let t := algebraicFullPrefixes family.init data.toAlgebraicWfProof j
  have hlen : t.val.length = adaptiveIpaRoundLen (shape := shape) family.init j :=
    algebraicFullPrefixes_length_eq_adaptiveIpaRoundLen family.init
      data.toAlgebraicWfProof j
  have hcoordinates := adaptiveIpaQueryCoordinates_eq_of_pinned family basis O j decoded pinned
  have hpre := preIpaTranscript_eq_of_fullPrefix_eq family.init decoded.proof
    data.toAlgebraicWfProof.proof j decoded.point_eq
  have hsplice : decoded.proof.1 = spliceIpa data.algebraicProof.erase
      decoded.proof.1.ipaRounds decoded.proof.1.ipaC decoded.proof.1.ipaF :=
    preIpaTranscript_inj family.init decoded.proof.2 data.wellFormed hpre
  have hcanonical : adaptiveIpaCanonicalProof decoded.proof.1 =
      adaptiveIpaCanonicalProof data.algebraicProof.erase := by
    rw [hsplice]
    rfl
  have hfinalCover := data.adaptiveIpaCanonicalCovered j
  have hqueryCover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm (family.vk basis) (family.instanceCommitment basis)
        (adaptiveIpaCanonicalProof decoded.proof.1)
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ (adaptiveIpaQueryCoordinates family.init basis j decoded pinned.query
          (family.fixedRepresentations basis)).multiopenSource, ap.point = pr.2 := by
    simpa only [hcanonical, hcoordinates] using hfinalCover
  unfold adaptiveQueriedIpaSurface adaptiveFallbackIpaSurface
  exact adaptiveIpaSurfaceCore_eq family basis j data t decoded pinned.query _ _ hlen
    hdecode hcanonical hcoordinates hqueryCover hfinalCover

theorem adaptiveIpaBad_eq_of_pinned
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (j : Fin shape.k)
    (decoded : DecodedIpaPrefix (shape := shape) family.init j
      (algebraicFullPrefixes family.init
        ((family.adversary basis).run O).toAlgebraicWfProof j))
    (hdecode : decodeIpaPrefix? (shape := shape) family.init j
      (algebraicFullPrefixes family.init
        ((family.adversary basis).run O).toAlgebraicWfProof j) = some decoded)
    (pinned : SelectedQueryRepresentationPinned
      (algebraicFullPrefixes family.init
        ((family.adversary basis).run O).toAlgebraicWfProof j)
      (family.adversary basis) O
      (((family.adversary basis).run O).algebraicProof.representationsBeforeRound j)) :
    adaptiveIpaQueriedBad family basis j
        (algebraicFullPrefixes family.init
          ((family.adversary basis).run O).toAlgebraicWfProof j)
        pinned.query O =
      adaptiveIpaFallbackBad family basis j ((family.adversary basis).run O)
        (algebraicFullPrefixes family.init
          ((family.adversary basis).run O).toAlgebraicWfProof j) O := by
  unfold adaptiveIpaQueriedBad adaptiveIpaFallbackBad
  exact adaptiveQueriedIpaSurface_eq_fallback_of_pinned family basis O j
    decoded hdecode pinned

theorem LabeledOracleComp.firstLabelOrFallbackBad_eq_fallback_of_findLabel_eq_none
    {T F α : Type*} {Label : T → Type*} [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (t : T) (O : T → F) (hfind : A.findLabel O t = none) :
    LabeledOracleComp.firstLabelOrFallbackBad A bad fallback t O =
      fallback (A.run O) t O := by
  unfold LabeledOracleComp.firstLabelOrFallbackBad
  rw [hfind]

theorem LabeledOracleComp.firstLabelOrFallbackBad_eq_bad_of_findLabel_eq_some
    {T F α : Type*} {Label : T → Type*} [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (t : T) (O : T → F) (label : Label t)
    (hfind : A.findLabel O t = some label) :
    LabeledOracleComp.firstLabelOrFallbackBad A bad fallback t O = bad t label O := by
  unfold LabeledOracleComp.firstLabelOrFallbackBad
  rw [hfind]

theorem LabeledOracleComp.mem_firstLabelOrFallbackBad_of_findLabel_eq_none
    {T F α : Type*} {Label : T → Type*} [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (t : T) (O : T → F) (x : F) (hfind : A.findLabel O t = none)
    (hx : x ∈ fallback (A.run O) t O) :
    x ∈ LabeledOracleComp.firstLabelOrFallbackBad A bad fallback t O := by
  rw [LabeledOracleComp.firstLabelOrFallbackBad_eq_fallback_of_findLabel_eq_none
    A bad fallback t O hfind]
  exact hx

theorem LabeledOracleComp.mem_firstLabelOrFallbackBad_of_findLabel_eq_some
    {T F α : Type*} {Label : T → Type*} [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (t : T) (O : T → F) (x : F) (label : Label t)
    (hfind : A.findLabel O t = some label) (hx : x ∈ bad t label O) :
    x ∈ LabeledOracleComp.firstLabelOrFallbackBad A bad fallback t O := by
  rw [LabeledOracleComp.firstLabelOrFallbackBad_eq_bad_of_findLabel_eq_some
    A bad fallback t O label hfind]
  exact hx

/-- The explicit formula agrees with the existing straight-line polynomial on final online data. -/
theorem OnlineMemberProofData.adaptiveIpaRootPolynomial_eq
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed)
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp) (j : Fin shape.k) :
    adaptiveIpaRootPolynomial vk instanceCommitment data.algebraicProof.erase
        data.adaptiveIpaCoordinates data.assemblyCovered nu chi j =
      data.toAlgebraicWfProof.straightLineIpaRootPolynomial nu chi j := by
  unfold adaptiveIpaRootPolynomial AlgebraicWfProof.straightLineIpaRootPolynomial
  rw [data.toAlgebraicWfProof.straightLineInitialDiscrepancy_eq nu]
  rfl

/-- Canonicalizing the unused IPA suffix does not change the initial straight-line data. -/
theorem OnlineMemberProofData.adaptiveIpaCanonicalRootPolynomial_eq
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed)
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp) (j : Fin shape.k) :
    adaptiveIpaRootPolynomial vk instanceCommitment
        (adaptiveIpaCanonicalProof data.algebraicProof.erase)
        data.adaptiveIpaCoordinates (by
          intro rho pr hpr
          exact data.assemblyCovered rho pr hpr) nu chi j =
      data.toAlgebraicWfProof.straightLineIpaRootPolynomial nu chi j := by
  unfold adaptiveIpaCanonicalProof
  rw [adaptiveIpaRootPolynomial_spliceIpa]
  exact data.adaptiveIpaRootPolynomial_eq nu chi j

end Zcash.Snark
