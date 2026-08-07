import Zcash.Common.RelationProbabilityCoins
import Zcash.Snark.Soundness.Decoded.Vesta
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.FiatShamir.Adversary.PreIpa
import Zcash.Snark.Soundness.FiatShamir.Adversary.DomainReduction

/-!
# Fiat–Shamir to AGM handoff

Decode a bounded-query adversary's deployed transcript into the representation-carrying proof the
AGM reduction consumes, and name the acceptance and binding-attack events on one oracle table.
`ComputedAlgebraicFSFamily` is the basis-indexed adversary family the straight-line route in
`Soundness.Composition.StraightLineDeployed` builds on; one run reads one table, so a family's
`Coins` is that table alone.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.zero)

open scoped ENNReal

local instance : Inhabited VestaG := ⟨0⟩

/-! ## Minimal deployed transcript interface -/

/-- A deployed proof string together with the reader's shape checks. -/
def WfProof (shape : Shape) : Type _ := {ps' : ProofString shape Fp VestaG // PsWellFormed ps'}

/-- The proof's eleven pre-IPA squeeze points, embedded in the bounded oracle domain. -/
def fullPrefixesPre {shape : Shape} (init : List (TranscriptElt Fp VestaG)) (p : WfProof shape) :
    Fin 11 → BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) :=
  fun i => ⟨preIpaSqueezePoints init p.1 i, by
    have h := (preIpaSqueezePoints_length_le init p.1 i).trans
      (le_of_eq (preIpaTranscript_length_eq init p.1 p.2))
    omega⟩

/-- The proof's IPA round transcripts, embedded in the bounded oracle domain. -/
def fullPrefixes {shape : Shape} (init : List (TranscriptElt Fp VestaG)) (p : WfProof shape) :
    Fin shape.k → BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) :=
  fun j => ⟨roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j, by
    rw [roundTranscriptFin_length, preIpaTranscript_length_eq init p.1 p.2]
    have := j.isLt
    omega⟩

/-- Read the two round points from the final absorb block before a challenge squeeze. -/
def grindDecode [Inhabited VestaG] {L : ℕ} (t : BTranscript Fp VestaG L) : VestaG × VestaG :=
  ((match t.val[t.val.length - 3]? with | some (.point g) => g | _ => default),
   (match t.val[t.val.length - 2]? with | some (.point g) => g | _ => default))

/-- Decoding a deployed round transcript returns that round's two points. -/
theorem grindDecode_round {L : ℕ} [Inhabited VestaG] {shape : Shape}
    (t₀ : List (TranscriptElt Fp VestaG)) (R : Fin shape.k → VestaG × VestaG) (j : Fin shape.k)
    (hb : (roundTranscriptFin t₀ R j).length ≤ L) :
    grindDecode (⟨roundTranscriptFin t₀ R j, hb⟩ : BTranscript Fp VestaG L) = R j := by
  have hlen : (roundTranscriptFin t₀ R j).length = t₀.length + 3 * (j.val + 1) :=
    roundTranscriptFin_length t₀ R j
  show ((match (roundTranscriptFin t₀ R j)[(roundTranscriptFin t₀ R j).length - 3]? with
      | some (.point g) => g | _ => default),
    (match (roundTranscriptFin t₀ R j)[(roundTranscriptFin t₀ R j).length - 2]? with
      | some (.point g) => g | _ => default)) = R j
  rw [show (roundTranscriptFin t₀ R j).length - 3 = t₀.length + 3 * j.val from by omega,
    show (roundTranscriptFin t₀ R j).length - 2 = t₀.length + 3 * j.val + 1 from by omega,
    roundTranscriptFin_getElem?_fst, roundTranscriptFin_getElem?_snd]

/-- Multiopen values do not depend on the IPA round challenges. -/
theorem multiopenValue_ipaRound [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (c : Challenges shape.k Fp) (χ : Fin shape.k → Fp) :
    multiopenValue vk instanceCommitment ps {c with ipaRound := χ} = multiopenValue vk instanceCommitment ps c := rfl

/-- Replacing the IPA proof suffix does not change the multiopen value. -/
theorem multiopenValue_spliceIpa [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (R : Fin shape.k → VestaG × VestaG) (cc ff : Fp)
    (c : Challenges shape.k Fp) :
    multiopenValue vk instanceCommitment (spliceIpa ps R cc ff) c = multiopenValue vk instanceCommitment ps c := rfl

/-- Multiopen commitments do not depend on the IPA round challenges. -/
theorem multiopenCommitment_ipaRound [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (g : Fin (2 ^ shape.k) → VestaG)
    (w u : VestaG) (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (c : Challenges shape.k Fp) (χ : Fin shape.k → Fp) :
    multiopenCommitment g w u vk instanceCommitment ps {c with ipaRound := χ}
      = multiopenCommitment g w u vk instanceCommitment ps c := rfl

/-- Replacing the IPA proof suffix does not change the multiopen commitment. -/
theorem multiopenCommitment_spliceIpa [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (g : Fin (2 ^ shape.k) → VestaG)
    (w u : VestaG) (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (R : Fin shape.k → VestaG × VestaG) (cc ff : Fp) (c : Challenges shape.k Fp) :
    multiopenCommitment g w u vk instanceCommitment (spliceIpa ps R cc ff) c
      = multiopenCommitment g w u vk instanceCommitment ps c := rfl

/-- Every pre-IPA squeeze position is no later than the final one. -/
private theorem preIpaLen_le_last (shape : Shape) (n₀ : ℕ) (i : Fin 11) :
    preIpaLen shape n₀ i ≤ preIpaLen shape n₀ 10 := by
  fin_cases i <;> simp [preIpaLen] <;> omega

attribute [local irreducible] preIpaTranscript preIpaLen

/-- Decode the deployed pre-IPA chain and IPA round chain from an adaptive proof output. -/
def fullDecodeDeployed [Inhabited VestaG] (shape : Shape)
    (init : List (TranscriptElt Fp VestaG)) :
    FullDecode (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) 11 shape.k
      (fullPrefixesPre init) (fullPrefixes init) :=
  { roundOf := fun t => (t.val.length - preIpaLen shape init.length 10) / 3 - 1
    chainAt := fun t i =>
      ⟨t.val.take (preIpaLen shape init.length 10 + 3 * (i.val + 1)), by
        rw [List.length_take]
        exact le_trans (min_le_right _ _) t.prop⟩
    roundOf_prefixes := by
      intro p j
      show (((roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j).length
          - preIpaLen shape init.length 10)) / 3 - 1 = j.val
      rw [roundTranscriptFin_length, preIpaTranscript_length_eq init p.1 p.2]
      omega
    chainAt_prefixes := by
      intro p j i hij
      apply Subtype.ext
      show (roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j).take
          (preIpaLen shape init.length 10 + 3 * (i.val + 1))
          = roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds i
      rw [← preIpaTranscript_length_eq init p.1 p.2]
      exact roundTranscriptFin_take (preIpaTranscript init p.1) p.1.ipaRounds hij
    chainAt_ne := by
      intro t i hi hEq
      have hi' : i.val < (t.val.length - preIpaLen shape init.length 10) / 3 - 1 := hi
      have hlen : (t.val.take (preIpaLen shape init.length 10 + 3 * (i.val + 1))).length
          = t.val.length :=
        congrArg (fun x : BTranscript Fp VestaG
          (preIpaLen shape init.length 10 + 3 * shape.k) => x.val.length) hEq
      rw [List.length_take] at hlen
      omega
    chainPre := fun t i =>
      ⟨t.val.take (preIpaLen shape init.length i), by
        rw [List.length_take]
        exact le_trans (min_le_right _ _) t.prop⟩
    guard := fun t => preIpaLen shape init.length 10 < t.val.length
    guard_prefixes := by
      intro p j
      show preIpaLen shape init.length 10
          < (roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j).length
      rw [roundTranscriptFin_length, preIpaTranscript_length_eq init p.1 p.2]
      omega
    chainPre_prefixes := by
      intro p j i
      apply Subtype.ext
      show (roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j).take
          (preIpaLen shape init.length i) = preIpaSqueezePoints init p.1 i
      have hpre : preIpaSqueezePoints init p.1 i
          <+: roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j :=
        (preIpaSqueezePoints_prefix init p.1 i).trans
          (by rw [roundTranscriptFin]; exact List.prefix_append _ _)
      have h := List.prefix_iff_eq_take.mp hpre
      rw [preIpaSqueezePoints_length_eq init p.1 p.2] at h
      exact h.symm
    chainPre_ne := by
      intro t hg i hEq
      have hlen : (t.val.take (preIpaLen shape init.length i)).length = t.val.length :=
        congrArg (fun x : BTranscript Fp VestaG
          (preIpaLen shape init.length 10 + 3 * shape.k) => x.val.length) hEq
      rw [List.length_take] at hlen
      have := preIpaLen_le_last shape init.length i
      have hg' : preIpaLen shape init.length 10 < t.val.length := hg
      omega }

/-! ## Algebraic output of the fully adaptive deployed adversary -/

/-- A proof string in which every prover-emitted group element carries its AGM representation. -/
abbrev AlgebraicProofString (shape : Shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :=
  ProofString shape Fp (AlgebraicPoint (F := Fp) basis)

namespace AlgebraicProofString

/-- Erase every group representation to obtain the deployed proof string. -/
def erase {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (ps : AlgebraicProofString shape basis) : ProofString shape Fp VestaG :=
  { adviceCommitments := fun p i => (ps.adviceCommitments p i).point
    lookupPermutedInput := fun p i => (ps.lookupPermutedInput p i).point
    lookupPermutedTable := fun p i => (ps.lookupPermutedTable p i).point
    permutationProduct := fun p i => (ps.permutationProduct p i).point
    lookupProduct := fun p i => (ps.lookupProduct p i).point
    vanishingRandom := ps.vanishingRandom.point
    hPieces := fun i => (ps.hPieces i).point
    instanceEvals := ps.instanceEvals
    adviceEvals := ps.adviceEvals
    fixedEvals := ps.fixedEvals
    vanishingRandomEval := ps.vanishingRandomEval
    permutationCommonEvals := ps.permutationCommonEvals
    permutationSetEvals := ps.permutationSetEvals
    lookupEvals := ps.lookupEvals
    multiopenQPrime := ps.multiopenQPrime.point
    multiopenU := ps.multiopenU
    ipaS := ps.ipaS.point
    ipaRounds := fun j => ((ps.ipaRounds j).1.point, (ps.ipaRounds j).2.point)
    ipaC := ps.ipaC
    ipaF := ps.ipaF }

end AlgebraicProofString

/-- An algebraic proof and its aggregate `(g,U,W)` coordinates after transcript assembly. -/
structure AlgebraicWfProof {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) where
  algebraicProof : AlgebraicProofString shape basis
  wellFormed : PsWellFormed algebraicProof.erase
  aMulti : (Fin 11 → Fp) → Fin (2 ^ shape.k) → Fp
  multiU : (Fin 11 → Fp) → Fp
  multiBlind : (Fin 11 → Fp) → Fp
  multiopen_repr : ∀ ν,
    commit (ursOfAugmentedBasis shape.k basis) (aMulti ν) +
        multiU ν • (ursOfAugmentedBasis shape.k basis).u +
        multiBlind ν • (ursOfAugmentedBasis shape.k basis).w =
      multiopenCommitment (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u
        vk instanceCommitment algebraicProof.erase (chRecord ν (fun _ => 0))
  s : Fin (2 ^ shape.k) → Fp
  sU : Fp
  sBlind : Fp
  ipaS_repr : commit (ursOfAugmentedBasis shape.k basis) s +
      sU • (ursOfAugmentedBasis shape.k basis).u +
      sBlind • (ursOfAugmentedBasis shape.k basis).w = algebraicProof.ipaS.point

namespace AlgebraicWfProof

/-- The ordinary well-formed proof used by the deployed transcript schedule. -/
def proof {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (p : AlgebraicWfProof basis vk instanceCommitment) : WfProof shape :=
  ⟨p.algebraicProof.erase, p.wellFormed⟩

/-- Representation-carrying IPA round points. -/
def rounds {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (p : AlgebraicWfProof basis vk instanceCommitment) (j : Fin shape.k) :
    AlgebraicPoint (F := Fp) basis × AlgebraicPoint (F := Fp) basis :=
  p.algebraicProof.ipaRounds j

end AlgebraicWfProof

/-- Precompose a fully adaptive decode with an erasure map on adversary outputs. -/
def FullDecode.precomp {T P P' : Type*} {m k : ℕ}
    {prefixesPre : P → Fin m → T} {prefixes : P → Fin k → T}
    (D : FullDecode T m k prefixesPre prefixes) (erase : P' → P) :
    FullDecode T m k (fun p => prefixesPre (erase p)) (fun p => prefixes (erase p)) :=
  { roundOf := D.roundOf
    chainAt := D.chainAt
    roundOf_prefixes := fun p j => D.roundOf_prefixes (erase p) j
    chainAt_prefixes := fun p j i h => D.chainAt_prefixes (erase p) j i h
    chainAt_ne := D.chainAt_ne
    chainPre := D.chainPre
    guard := D.guard
    guard_prefixes := fun p j => D.guard_prefixes (erase p) j
    chainPre_prefixes := fun p j i => D.chainPre_prefixes (erase p) j i
    chainPre_ne := D.chainPre_ne }

/-- The algebraic output's pre-IPA squeeze points. -/
def algebraicFullPrefixesPre {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk instanceCommitment) :=
  fullPrefixesPre init p.proof

/-- The algebraic output's IPA round squeeze points. -/
def algebraicFullPrefixes {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk instanceCommitment) :=
  fullPrefixes init p.proof

/-- Equality of one deployed IPA squeeze point fixes the complete pre-IPA transcript. -/
theorem preIpaTranscript_eq_of_fullPrefix_eq {shape : Shape}
    (init : List (TranscriptElt Fp VestaG)) (p q : WfProof shape) (j : Fin shape.k)
    (h : fullPrefixes init p j = fullPrefixes init q j) :
    preIpaTranscript init p.1 = preIpaTranscript init q.1 := by
  have hval := congrArg Subtype.val h
  change roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j =
    roundTranscriptFin (preIpaTranscript init q.1) q.1.ipaRounds j at hval
  have hp := preIpaTranscript_length_eq init p.1 p.2
  have hq := preIpaTranscript_length_eq init q.1 q.2
  rw [roundTranscriptFin, roundTranscriptFin] at hval
  calc
    preIpaTranscript init p.1 =
        (preIpaTranscript init p.1 ++
          (((List.finRange shape.k).take (j.val + 1)).map (fun i =>
            [TranscriptElt.point (p.1.ipaRounds i).1,
              TranscriptElt.point (p.1.ipaRounds i).2,
              TranscriptElt.challenge])).flatten).take (preIpaLen shape init.length 10) := by
          rw [← hp, List.take_append_of_le_length (le_refl _)]
          simp
    _ = (preIpaTranscript init q.1 ++
          (((List.finRange shape.k).take (j.val + 1)).map (fun i =>
            [TranscriptElt.point (q.1.ipaRounds i).1,
              TranscriptElt.point (q.1.ipaRounds i).2,
              TranscriptElt.challenge])).flatten).take (preIpaLen shape init.length 10) :=
        congrArg (List.take (preIpaLen shape init.length 10)) hval
    _ = preIpaTranscript init q.1 := by
          rw [← hq, List.take_append_of_le_length (le_refl _)]
          simp

/-- Acceptance with a carried aggregate opening that mismatches the accepted value. -/
def fullAlgebraicBindingAttack {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (p : AlgebraicWfProof basis vk instanceCommitment)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp) : Prop :=
  DeployedIpaVerifierEq (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u
      vk instanceCommitment p.proof.1 (chRecord ν χ) ∧
    innerProduct (p.aMulti ν) (evalVector shape.k (ν 7)) ≠
      multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) +
        (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU) -
        ν 9 * innerProduct p.s (evalVector shape.k (ν 7))

/-- The binding attack with the `z ≠ 0` guard used by the straight-line classifier. -/
def fullAlgebraicBindingAttackZ {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (p : AlgebraicWfProof basis vk instanceCommitment)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp) : Prop :=
  fullAlgebraicBindingAttack basis vk instanceCommitment p ν χ ∧ ν 10 ≠ 0

/-- Plain deployed verifier acceptance, with no folding-challenge guard. `fullAlgebraicAcceptZ` is
this conjoined with `ν 10 ≠ 0`; the `z = 0` slice is priced separately. -/
def fullAlgebraicAccept {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (p : AlgebraicWfProof basis vk instanceCommitment)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp) : Prop :=
  DeployedIpaVerifierEq (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u
      vk instanceCommitment p.proof.1 (chRecord ν χ)

/-- Verifier acceptance with the nonzero folding challenge required by extraction. -/
def fullAlgebraicAcceptZ {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (p : AlgebraicWfProof basis vk instanceCommitment)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp) : Prop :=
  DeployedIpaVerifierEq (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u
      vk instanceCommitment p.proof.1 (chRecord ν χ) ∧ ν 10 ≠ 0

/-- The accepting-transcript test read directly from one oracle table. -/
def algebraicTableAcceptZ {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (p : AlgebraicWfProof basis vk instanceCommitment) : Prop :=
  fullAlgebraicAcceptZ basis vk instanceCommitment p
    (fun i => O (algebraicFullPrefixesPre init p i))
    (fun j => O (algebraicFullPrefixes init p j))

/-! ## The computed adversary family -/

/-- A basis-indexed family with one common transcript prefix, so every basis uses the same oracle
table type. -/
structure ComputedAlgebraicFSFamily (shape : Shape) where
  init : List (TranscriptElt Fp VestaG)
  vk : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → VerifyingKey shape Fp VestaG
  instanceCommitment : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → Fin shape.numProofs → ℕ → VestaG
  adversary : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → OracleComp
    (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
    (AlgebraicWfProof basis (vk basis) (instanceCommitment basis))
  Q : ℕ
  queryBound : ∀ basis, (adversary basis).QueryBound Q

namespace ComputedAlgebraicFSFamily

variable {shape : Shape}

/-- The random-oracle table read by one adversary execution. -/
abbrev Coins (family : ComputedAlgebraicFSFamily shape) :=
  BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp

end ComputedAlgebraicFSFamily

/-! ## Unbounded oracle domain

Bounded-query adversaries over transcript lists reduce to their finite reachable-support split.
Blake2b remains idealized; `truncateTranscript` is only the deployed bounded-transcript retraction. -/

/-- Transfer a uniform bounded-transcript binding bound to the reachable-support split. This is the
named reduction from the unbounded oracle domain to its finite reachable-support split. -/
theorem bindingWin_unbounded_measure_le {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG} {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp (List (TranscriptElt Fp VestaG)) Fp (AlgebraicWfProof basis vk instanceCommitment))
    {Q : ℕ} (hQ : A.QueryBound Q) {β : ℝ≥0∞}
    (hβ : ∀ A₀ : OracleComp
        (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
        (AlgebraicWfProof basis vk instanceCommitment), A₀.QueryBound Q →
      (PMF.uniformOfFintype
          (BTranscript Fp VestaG
            (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
        {O | fsWinsFull A₀ (fullAlgebraicBindingAttack basis vk instanceCommitment)
          (algebraicFullPrefixesPre init) (algebraicFullPrefixes init) O} ≤ β) :
    (PMF.uniformOfFintype
        ((BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) ⊕
            {t // t ∈ A.reachSet}) → Fp)).toOuterMeasure
      {O' | fsWinsFull
        (A.splitDomain
          (Subtype.val : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) →
            List (TranscriptElt Fp VestaG))
          (truncateTranscript (preIpaLen shape init.length 10 + 3 * shape.k))
          A.reachSet (Finset.Subset.refl _))
        (fullAlgebraicBindingAttack basis vk instanceCommitment)
        (fun p i => Sum.inl (algebraicFullPrefixesPre init p i))
        (fun p j => Sum.inl (algebraicFullPrefixes init p j)) O'} ≤ β :=
  fsWinsFull_unbounded_measure_le
    (T := List (TranscriptElt Fp VestaG))
    (T_D := BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k))
    Subtype.val
    (truncateTranscript (preIpaLen shape init.length 10 + 3 * shape.k))
    A hQ (fullAlgebraicBindingAttack basis vk instanceCommitment)
    (algebraicFullPrefixesPre init) (algebraicFullPrefixes init) hβ

/-! ## Uniform-URS basis transfer -/

/-- Transfer any finite-coin event across a uniform-URS basis identification. The statement is
route-independent and reusable by programmed-basis arguments. -/
theorem uniformURS_basis_transfer {k : ℕ} {C : Type*} [Fintype C] [Nonempty C]
    {Ω : Type*} (setup : PMF Ω) (B : VestaG)
    (basisOf : Ω → AugmentedIndex (2 ^ k) → VestaG)
    (E : Set ((AugmentedIndex (2 ^ k) → VestaG) × C))
    (hURS : OrchardUniformURSIdentification setup k B basisOf) :
    (independentProductPMF setup (PMF.uniformOfFintype C)).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' E) =
      (PMF.uniformOfFintype ((AugmentedIndex (2 ^ k) → Fp) × C)).toOuterMeasure
        ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' E) := by
  let coinPMF := PMF.uniformOfFintype C
  have hprod :
      (independentProductPMF setup coinPMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)) coinPMF).map
            (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) coinPMF :=
        independentProductPMF_map_left setup coinPMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).map (scalarBasis B))
          coinPMF := congrArg (fun p => independentProductPMF p coinPMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)) coinPMF
        (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex (2 ^ k) → VestaG) × C) => p.toOuterMeasure E) hprod
  change ((independentProductPMF setup coinPMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure E =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)) coinPMF).map
        (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure E at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  rw [hmeasure, independentProductPMF_uniform]

/-! ## Standard AGM adapter

Compute multiopen and `S` coordinates from representations of the points used by the assembly. -/

/-- Decompose an augmented-basis representation into its generator, `U`, and `W` components. -/
theorem representationEval_augmented_components {n : ℕ}
    (basis : AugmentedIndex n → VestaG) (c : AugmentedIndex n → Fp) :
    representationEval basis c
      = (∑ i : Fin n, c (AugmentedIndex.gen i) • basis (AugmentedIndex.gen i))
        + c AugmentedIndex.u • basis AugmentedIndex.u
        + c AugmentedIndex.w • basis AugmentedIndex.w := by
  rw [representationEval, Fintype.sum_sum_type, Fin.sum_univ_two, ← add_assoc]
  rfl

section Adapter

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}

/-- The generator components of an augmented-basis representation. -/
def _root_.Zcash.AlgebraicPoint.gPart (P : AlgebraicPoint (F := Fp) basis) :
    Fin (2 ^ shape.k) → Fp :=
  fun i => P.coeffs (AugmentedIndex.gen i)

/-- An augmented-basis point is its generator commitment plus its declared `U` and `W`
components. -/
theorem _root_.Zcash.AlgebraicPoint.point_eq_components (P : AlgebraicPoint (F := Fp) basis) :
    P.point = commit (ursOfAugmentedBasis shape.k basis) P.gPart
      + P.coeffs AugmentedIndex.u • (ursOfAugmentedBasis shape.k basis).u
      + P.coeffs AugmentedIndex.w • (ursOfAugmentedBasis shape.k basis).w := by
  rw [← P.hEq, representationEval_augmented_components]
  rfl

private theorem commitA_add (a b : Fin (2 ^ shape.k) → Fp) :
    commit (ursOfAugmentedBasis shape.k basis) (a + b)
      = commit (ursOfAugmentedBasis shape.k basis) a
        + commit (ursOfAugmentedBasis shape.k basis) b :=
  commit_add _ _ _

private theorem commitA_smul (c : Fp) (a : Fin (2 ^ shape.k) → Fp) :
    commit (ursOfAugmentedBasis shape.k basis) (c • a)
      = c • commit (ursOfAugmentedBasis shape.k basis) a :=
  commit_smul _ _ _

/-- The aggregated generator coordinates of a represented term list. -/
def repsGPart (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) : Fin (2 ^ shape.k) → Fp :=
  fun i => (reps.map (fun t => t.1 * t.2.coeffs (AugmentedIndex.gen i))).sum

/-- The aggregated `U` coordinate of a represented term list. -/
def repsU (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) : Fp :=
  (reps.map (fun t => t.1 * t.2.coeffs AugmentedIndex.u)).sum

/-- The aggregated `W` coordinate of a represented term list. -/
def repsW (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) : Fp :=
  (reps.map (fun t => t.1 * t.2.coeffs AugmentedIndex.w)).sum

theorem repsGPart_cons (t : Fp × AlgebraicPoint (F := Fp) basis)
    (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) :
    repsGPart (t :: reps) = t.1 • t.2.gPart + repsGPart reps := by
  funext i
  simp [repsGPart, AlgebraicPoint.gPart, smul_eq_mul]

theorem repsU_cons (t : Fp × AlgebraicPoint (F := Fp) basis)
    (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) :
    repsU (t :: reps) = t.1 * t.2.coeffs AugmentedIndex.u + repsU reps := by
  simp [repsU]

theorem repsW_cons (t : Fp × AlgebraicPoint (F := Fp) basis)
    (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) :
    repsW (t :: reps) = t.1 * t.2.coeffs AugmentedIndex.w + repsW reps := by
  simp [repsW]

/-- Sum represented terms by aggregating their generator, `U`, and `W` coordinates. -/
theorem sum_map_smul_point_repr (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) :
    ((reps.map (fun t => (t.1, t.2.point))).map (fun t => t.1 • t.2)).sum
      = commit (ursOfAugmentedBasis shape.k basis) (repsGPart reps)
        + repsU reps • (ursOfAugmentedBasis shape.k basis).u
        + repsW reps • (ursOfAugmentedBasis shape.k basis).w := by
  induction reps with
  | nil =>
      simp [repsGPart, repsU, repsW, commit]
  | cons t reps ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, t.2.point_eq_components, repsGPart_cons, repsU_cons, repsW_cons,
        commitA_add, commitA_smul]
      module

/-- Evaluate an MSM from its native scalars and representations of appended points. -/
theorem Msm.eval_repr (m : Msm shape.k Fp VestaG)
    (reps : List (Fp × AlgebraicPoint (F := Fp) basis))
    (hcov : m.other = reps.map (fun t => (t.1, t.2.point))) :
    m.eval (ursOfAugmentedBasis shape.k basis)
      = commit (ursOfAugmentedBasis shape.k basis) (m.gScalars + repsGPart reps)
        + (m.uScalar + repsU reps) • (ursOfAugmentedBasis shape.k basis).u
        + (m.wScalar + repsW reps) • (ursOfAugmentedBasis shape.k basis).w := by
  have heval : ∀ (urs : URS VestaG) (m' : Msm urs.k Fp VestaG),
      m'.eval urs = commit urs m'.gScalars + m'.wScalar • urs.w + m'.uScalar • urs.u
        + (m'.other.map fun t => t.1 • t.2).sum := fun _ _ => rfl
  rw [heval, hcov, sum_map_smul_point_repr, commitA_add]
  module

/-- The multiopen assembly MSM whose evaluation is `multiopenCommitment`. -/
def multiopenMsm (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp) :
    Msm shape.k Fp VestaG :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) (Msm.zero shape.k Fp VestaG)).1

/-- `multiopenCommitment` is the assembly MSM's evaluation. -/
theorem multiopenCommitment_eq_eval
    (g' : Fin (2 ^ shape.k) → VestaG) (w' u' : VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp) :
    multiopenCommitment g' w' u' vk instanceCommitment ps ch
      = (multiopenMsm vk instanceCommitment ps ch).eval ⟨shape.k, g', w', u'⟩ := by
  unfold multiopenCommitment multiopenMsm
  rfl

attribute [local irreducible] multiopenMsm

/-- Evaluating against the reconstructed URS is invariant under structure eta. -/
private theorem eval_urs_eta (m : Msm shape.k Fp VestaG) :
    m.eval (⟨shape.k, (ursOfAugmentedBasis shape.k basis).g,
        (ursOfAugmentedBasis shape.k basis).w,
        (ursOfAugmentedBasis shape.k basis).u⟩ : URS VestaG)
      = m.eval (ursOfAugmentedBasis shape.k basis) := rfl

attribute [local irreducible] multiopenCommitment Msm.eval

/-- Representations for every point appended by an arbitrary MSM. -/
structure RepresentedMsm (m : Msm shape.k Fp VestaG)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) where
  reps : List (Fp × AlgebraicPoint (F := Fp) basis)
  covers : m.other = reps.map (fun t => (t.1, t.2.point))

/-- Representations for every point appended by the multiopen assembly. -/
structure RepresentedMultiopen
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (ν : Fin 11 → Fp) where
  reps : List (Fp × AlgebraicPoint (F := Fp) basis)
  covers : (multiopenMsm vk instanceCommitment ps (chRecord ν (fun _ => 0))).other
    = reps.map (fun t => (t.1, t.2.point))

/-- Rebuild a scalar–point list from lookups into a covering list of represented points. -/
private theorem list_eq_map_pmap_lookup {β : Type*} (point : β → VestaG)
    (L : List β) : (l : List (Fp × VestaG)) →
    (H : ∀ pr ∈ l, (L.find? (fun ap => point ap = pr.2)).isSome) →
    l = (l.pmap (fun pr h => (pr.1, (L.find? (fun ap => point ap = pr.2)).get h)) H).map
        (fun t => (t.1, point t.2))
  | [], _ => rfl
  | pr :: l, H => by
      simp only [List.pmap, List.map_cons]
      refine congrArg₂ List.cons ?_ (list_eq_map_pmap_lookup point L l
        (fun a ha => H a (List.mem_cons_of_mem _ ha)))
      have hp := List.find?_some
        ((Option.some_get (H pr (List.mem_cons_self ..))).symm)
      have hpt : point ((L.find? (fun ap => point ap = pr.2)).get
          (H pr (List.mem_cons_self ..))) = pr.2 := by
        simpa using hp
      exact Prod.ext rfl hpt.symm

/-- Build an arbitrary represented MSM from a list covering every appended point. -/
def RepresentedMsm.ofCoveredList (m : Msm shape.k Fp VestaG)
    (L : List (AlgebraicPoint (F := Fp) basis))
    (hcover : ∀ pr ∈ m.other, ∃ ap ∈ L, ap.point = pr.2) :
    RepresentedMsm m basis :=
  have H : ∀ pr ∈ m.other,
      (L.find? (fun ap => ap.point = pr.2)).isSome := by
    intro pr hpr
    rw [List.find?_isSome]
    obtain ⟨ap, hapL, hap⟩ := hcover pr hpr
    exact ⟨ap, hapL, by simp [hap]⟩
  { reps := m.other.pmap
      (fun pr h => (pr.1, (L.find? (fun ap => ap.point = pr.2)).get h)) H
    covers := list_eq_map_pmap_lookup AlgebraicPoint.point L _ H }

/-- Build the represented assembly from a list covering every appended point. -/
def RepresentedMultiopen.ofCoveredList
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ν : Fin 11 → Fp) (L : List (AlgebraicPoint (F := Fp) basis))
    (hcover : ∀ pr ∈ (multiopenMsm vk instanceCommitment ps (chRecord ν (fun _ => 0))).other,
      ∃ ap ∈ L, ap.point = pr.2) :
    RepresentedMultiopen vk instanceCommitment ps basis ν :=
  have H : ∀ pr ∈ (multiopenMsm vk instanceCommitment ps (chRecord ν (fun _ => 0))).other,
      (L.find? (fun ap => ap.point = pr.2)).isSome := by
    intro pr hpr
    rw [List.find?_isSome]
    obtain ⟨ap, hapL, hap⟩ := hcover pr hpr
    exact ⟨ap, hapL, by simp [hap]⟩
  { reps := (multiopenMsm vk instanceCommitment ps (chRecord ν (fun _ => 0))).other.pmap
      (fun pr h => (pr.1, (L.find? (fun ap => ap.point = pr.2)).get h)) H
    covers := list_eq_map_pmap_lookup AlgebraicPoint.point L _ H }

/-- Package represented emitted points and their represented multiopen assembly. -/
def AlgebraicWfProof.ofRepresented {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase)
    (rm : ∀ ν : Fin 11 → Fp, RepresentedMultiopen vk instanceCommitment aps.erase basis ν) :
    AlgebraicWfProof basis vk instanceCommitment :=
  { algebraicProof := aps
    wellFormed := hwf
    aMulti := fun ν =>
      (multiopenMsm vk instanceCommitment aps.erase (chRecord ν (fun _ => 0))).gScalars + repsGPart (rm ν).reps
    multiU := fun ν =>
      (multiopenMsm vk instanceCommitment aps.erase (chRecord ν (fun _ => 0))).uScalar + repsU (rm ν).reps
    multiBlind := fun ν =>
      (multiopenMsm vk instanceCommitment aps.erase (chRecord ν (fun _ => 0))).wScalar + repsW (rm ν).reps
    multiopen_repr := fun ν =>
      (Msm.eval_repr (multiopenMsm vk instanceCommitment aps.erase (chRecord ν (fun _ => 0)))
        (rm ν).reps (rm ν).covers).symm.trans
        ((eval_urs_eta (multiopenMsm vk instanceCommitment aps.erase (chRecord ν (fun _ => 0)))).symm.trans
          (multiopenCommitment_eq_eval _ _ _ vk instanceCommitment aps.erase _).symm)
    s := aps.ipaS.gPart
    sU := aps.ipaS.coeffs AugmentedIndex.u
    sBlind := aps.ipaS.coeffs AugmentedIndex.w
    ipaS_repr := (AlgebraicPoint.point_eq_components aps.ipaS).symm }

end Adapter

end Zcash.Snark
