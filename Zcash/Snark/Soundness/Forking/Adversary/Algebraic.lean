import Zcash.Snark.Soundness.Vesta
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.AGM.ProbabilityCoins
import Zcash.Snark.Soundness.Forking.Adversary.PreIpa
import Zcash.Snark.Soundness.Forking.Adversary.Recursive
import Zcash.Snark.Soundness.Forking.Adversary.DomainReduction

/-!
# Fiat–Shamir to AGM handoff

Run the recursive extractor on a bounded-query adversary and package its certificate for the AGM
reduction. Acceptance with an opening mismatch yields a relation.

## Why the route ends in several endpoints

The `snarkFailure_prob_le_of_*` bounds are a cross-product, not restatements of one another: the
discrete-log flavour (textbook, folded, uniform-URS, generator-RO) against the adversary model
(query-bounded, unbounded, privately randomized). Each names a different hypothesis set, so a caller
picks the one whose assumptions it can actually supply. A handful of endpoints here is the intended
shape; what is not intended is two endpoints proving the same thing because a stacked branch left an
earlier form behind.
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

/-- Replacing the IPA proof suffix does not change the adjusted commitment: the splice rewrites only
`ipaRounds`/`ipaC`/`ipaF`, while `P' = P − [v]g₀ + [ξ]S` reads the multiopen fields and `ipaS`. -/
theorem deployedIpaCommitment_spliceIpa [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (g : Fin (2 ^ shape.k) → VestaG)
    (w u : VestaG) (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (R : Fin shape.k → VestaG × VestaG) (cc ff : Fp) (c : Challenges shape.k Fp) :
    deployedIpaCommitment g w u vk instanceCommitment (spliceIpa ps R cc ff) c
      = deployedIpaCommitment g w u vk instanceCommitment ps c := rfl

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

/-- The binding attack with the `z ≠ 0` guard required by the fork kernel. -/
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

/-- Run the recursive extractor against the deployed algebraic Fiat–Shamir adversary. The oracle
table and extractor coins determine the returned certificate. -/
def algebraicForkCertAttempt {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk instanceCommitment))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (coins : RecursiveForkCoins Fp shape.k) :
    RecursiveForkAttempt (AlgebraicDForkCert (F := Fp) basis shape.k) :=
  recursiveAlgebraicFork basis shape.k A (algebraicFullPrefixes init)
    (fun p => p.rounds) (fun p => (p.proof.1.ipaC, p.proof.1.ipaF))
    (algebraicTableAcceptZ basis vk instanceCommitment init) (fun O p => by
      unfold algebraicTableAcceptZ fullAlgebraicAcceptZ DeployedIpaVerifierEq
      infer_instance) O coins

/-- Accepted deployed algebraic FS runs on which the executable recursive extractor fails to
return a certificate. -/
noncomputable def algebraicForkCertFailureSet {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk instanceCommitment))
    (coins : RecursiveForkCoins Fp shape.k) :
    Set (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) :=
  {O | fsWinsFull A (fullAlgebraicAcceptZ basis vk instanceCommitment)
      (algebraicFullPrefixesPre init) (algebraicFullPrefixes init) O ∧
    ¬ (algebraicForkCertAttempt basis vk instanceCommitment init A O coins).output.isSome}

/-- The concrete recursive certificate producer loses only the bounded-query escape slice. -/
theorem algebraicForkCertFailure_measure_le {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk instanceCommitment))
    (tape : RecursiveForkTape Fp shape.k) {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
        (algebraicForkCertFailureSet basis vk instanceCommitment init A tape.toCoins)
      ≤ (Q + shape.k) * (3 / Fintype.card Fp) := by
  let D : PrefixDecode
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) shape.k
      (algebraicFullPrefixes (basis := basis) (vk := vk) (instanceCommitment := instanceCommitment) init) :=
    ((fullDecodeDeployed shape init).precomp
      (fun p : AlgebraicWfProof basis vk instanceCommitment => p.proof)).toPrefixDecode
  have h := recursiveForkFailure_measure_le basis shape.k A (algebraicFullPrefixes init)
    (fun p => p.rounds) (fun p => (p.proof.1.ipaC, p.proof.1.ipaF))
    (algebraicTableAcceptZ basis vk instanceCommitment init) (fun O p => by
      unfold algebraicTableAcceptZ fullAlgebraicAcceptZ DeployedIpaVerifierEq
      infer_instance) D tape.toCoins tape.toCoins_complete hQ
  simpa only [recursiveForkFailureSet, algebraicForkCertFailureSet, algebraicForkCertAttempt,
    algebraicTableAcceptZ, fsWinsFull] using h

/-- Every certificate returned by the deployed extractor satisfies `DeployedForkValid`. -/
theorem algebraicForkCertAttempt_valid {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk instanceCommitment))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (coins : RecursiveForkCoins Fp shape.k)
    (cert : AlgebraicDForkCert (F := Fp) basis shape.k)
    (hout : (algebraicForkCertAttempt basis vk instanceCommitment init A O coins).output = some cert) :
    let p₀ := A.run O
    let ν₀ : Fin 11 → Fp := fun i => O (algebraicFullPrefixesPre init p₀ i)
    let urs := ursOfAugmentedBasis shape.k basis
    DeployedForkValid urs.g (evalVector shape.k (ν₀ 7)) urs.u urs.w (ν₀ 10)
      (commit urs
          (adjustedWitness (p₀.aMulti ν₀) p₀.s
            (multiopenValue vk instanceCommitment p₀.proof.1 (chRecord ν₀ (fun _ => 0))) (ν₀ 9)) +
        (p₀.multiU ν₀ + ν₀ 9 * p₀.sU) • urs.u +
        (p₀.multiBlind ν₀ + ν₀ 9 * p₀.sBlind) • urs.w)
      cert.toDForkCert := by
  let p₀ := A.run O
  let ν₀ : Fin 11 → Fp := fun i => O (algebraicFullPrefixesPre init p₀ i)
  let urs := ursOfAugmentedBasis shape.k basis
  let FD : FullDecode
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k))
      11 shape.k (algebraicFullPrefixesPre init) (algebraicFullPrefixes init) :=
    (fullDecodeDeployed shape init).precomp
      (fun p : AlgebraicWfProof basis vk instanceCommitment => p.proof)
  let D := FD.toPrefixDecode
  let stable := fun
      (O' : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
      (p' : AlgebraicWfProof basis vk instanceCommitment) =>
    preIpaTranscript init p'.proof.1 = preIpaTranscript init p₀.proof.1 ∧
      ∀ i, O' (algebraicFullPrefixesPre init p' i) = ν₀ i
  have hstable₀ : stable O p₀ := by
    refine ⟨rfl, ?_⟩
    intro i
    rfl
  have hstableUpdate : ∀ (m : ℕ) (hm : m < shape.k)
      (O' : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
      (p' : AlgebraicWfProof basis vk instanceCommitment) (u : Fp), stable O' p' →
      let t := algebraicFullPrefixes init p' ⟨m, hm⟩
      let O'' := Function.update O' t u
      let p'' := A.run O''
      algebraicFullPrefixes init p'' ⟨m, hm⟩ = t → stable O'' p'' := by
    intro m hm O' p' u hs t O'' p'' ht
    change (preIpaTranscript init p'.proof.1 = preIpaTranscript init p₀.proof.1 ∧
      ∀ i, O' (algebraicFullPrefixesPre init p' i) = ν₀ i) at hs
    change preIpaTranscript init p''.proof.1 = preIpaTranscript init p₀.proof.1 ∧
      ∀ i, O'' (algebraicFullPrefixesPre init p'' i) = ν₀ i
    have hpre : preIpaTranscript init p''.proof.1 = preIpaTranscript init p'.proof.1 := by
      exact preIpaTranscript_eq_of_fullPrefix_eq init p''.proof p'.proof ⟨m, hm⟩ ht
    have hsplice : p''.proof.1 =
        spliceIpa p'.proof.1 p''.proof.1.ipaRounds p''.proof.1.ipaC p''.proof.1.ipaF :=
      preIpaTranscript_inj init p''.proof.2 p'.proof.2 hpre
    refine ⟨hpre.trans hs.1, ?_⟩
    intro i
    have hprePoint : algebraicFullPrefixesPre init p'' i =
        algebraicFullPrefixesPre init p' i := by
      apply Subtype.ext
      change preIpaSqueezePoints init p''.proof.1 i = preIpaSqueezePoints init p'.proof.1 i
      rw [hsplice, preIpaSqueezePoints_spliceIpa]
    have hne : algebraicFullPrefixesPre init p'' i ≠ t := by
      intro heq
      have hle := (preIpaSqueezePoints_length_le init p''.proof.1 i).trans
        (le_of_eq (preIpaTranscript_length_eq init p''.proof.1 p''.proof.2))
      have hround := roundTranscriptFin_length
        (preIpaTranscript init p'.proof.1) p'.proof.1.ipaRounds ⟨m, hm⟩
      rw [preIpaTranscript_length_eq init p'.proof.1 p'.proof.2] at hround
      have hlen := congrArg (fun x => x.val.length) heq
      change (preIpaSqueezePoints init p''.proof.1 i).length =
        (roundTranscriptFin (preIpaTranscript init p'.proof.1)
          p'.proof.1.ipaRounds ⟨m, hm⟩).length at hlen
      omega
    change Function.update O' t u (algebraicFullPrefixesPre init p'' i) = ν₀ i
    rw [Function.update_apply, if_neg hne, hprePoint]
    exact hs.2 i
  have hdecode : ∀ (p : AlgebraicWfProof basis vk instanceCommitment) (j : Fin shape.k),
      ((p.rounds j).1.point, (p.rounds j).2.point) =
        grindDecode (algebraicFullPrefixes init p j) := by
    intro p j
    exact (grindDecode_round (preIpaTranscript init p.proof.1) p.proof.1.ipaRounds j _).symm
  have hreal : AlgebraicForkRealizes basis grindDecode
      (RecursiveRunSuffix shape.k 0 shape.k (by omega) A (algebraicFullPrefixes init)
        (fun p => (p.proof.1.ipaC, p.proof.1.ipaF))
        (algebraicTableAcceptZ basis vk instanceCommitment init) stable Fin.elim0) cert := by
    apply recursiveAlgebraicForkFrom_realizes basis shape.k A (algebraicFullPrefixes init)
      (fun p => p.rounds) (fun p => (p.proof.1.ipaC, p.proof.1.ipaF))
      (algebraicTableAcceptZ basis vk instanceCommitment init) _ grindDecode D stable hstableUpdate hdecode
      0 (by omega) O p₀ coins cert Fin.elim0 rfl hstable₀
    · intro i
      exact Fin.elim0 i
    · simpa only [algebraicForkCertAttempt, recursiveAlgebraicFork] using hout
  -- Stated in the adjusted commitment's components, not through `deployedIpaCommitment`: the
  -- rewrites below act on those components, and the abbrev is reducible, so `exact hacc` still
  -- bridges the two forms at the use site.
  have hPwhole : ∀ (chi : Fin shape.k → Fp),
      (multiopenCommitment urs.g urs.w urs.u vk instanceCommitment p₀.proof.1 (chRecord ν₀ chi)
        + (∑ i, ([-(multiopenValue vk instanceCommitment p₀.proof.1 (chRecord ν₀ chi))].getD i.val 0) • urs.g i)
        + (chRecord ν₀ chi : Challenges shape.k Fp).xi • p₀.proof.1.ipaS)
      = (commit urs
            (adjustedWitness (p₀.aMulti ν₀) p₀.s
              (multiopenValue vk instanceCommitment p₀.proof.1 (chRecord ν₀ (fun _ => 0))) (ν₀ 9))
          + (p₀.multiU ν₀ + ν₀ 9 * p₀.sU) • urs.u
          + (p₀.multiBlind ν₀ + ν₀ 9 * p₀.sBlind) • urs.w) := by
    intro chi
    dsimp only [urs]
    dsimp only [AlgebraicWfProof.proof]
    rw [← chRecord_update ν₀ chi, multiopenValue_ipaRound, multiopenCommitment_ipaRound,
      show ({chRecord ν₀ (fun _ => (0 : Fp)) with ipaRound := chi} :
        Challenges shape.k Fp).xi = ν₀ 9 from rfl,
      ← p₀.multiopen_repr ν₀,
      show p₀.algebraicProof.erase.ipaS = p₀.algebraicProof.ipaS.point from rfl,
      ← p₀.ipaS_repr,
      sum_getD_single urs.g
        (multiopenValue vk instanceCommitment p₀.algebraicProof.erase (chRecord ν₀ (fun _ => 0))),
      commit_adjustedWitness]
    module
  apply AlgebraicForkRealizes.deployedForkValid basis grindDecode urs.u urs.w (ν₀ 10)
    urs.g (evalVector shape.k (ν₀ 7)) _ _ cert hreal
  rintro ts cs c f ⟨O', p', hp', hwin, hs, -, hts, hcs, hfinal⟩
  change flatAccept (proverOfRounds (fun j => grindDecode (ts j)) c f)
    urs.g (evalVector shape.k (ν₀ 7)) urs.u urs.w (ν₀ 10)
      (commit urs
          (adjustedWitness (p₀.aMulti ν₀) p₀.s
            (multiopenValue vk instanceCommitment p₀.proof.1 (chRecord ν₀ (fun _ => 0))) (ν₀ 9)) +
        (p₀.multiU ν₀ + ν₀ 9 * p₀.sU) • urs.u +
        (p₀.multiBlind ν₀ + ν₀ 9 * p₀.sBlind) • urs.w) cs
  have hsplice : p'.proof.1 =
      spliceIpa p₀.proof.1 p'.proof.1.ipaRounds p'.proof.1.ipaC p'.proof.1.ipaF :=
    preIpaTranscript_inj init p'.proof.2 p₀.proof.2 hs.1
  have hnu : (fun i => O' (algebraicFullPrefixesPre init p' i)) = ν₀ := funext hs.2
  have hchi : (fun j => O' (algebraicFullPrefixes init p' j)) = cs := by
    funext j
    rw [show algebraicFullPrefixes init p' j = ts j by simpa using hts j]
    exact hcs j
  rw [algebraicTableAcceptZ, hnu, hchi] at hwin
  have hacc := hwin.1
  rw [deployedVerifierEq_iff_flatAccept] at hacc
  rw [hsplice, deployedIpaCommitment_spliceIpa] at hacc
  have hrounds : (fun j => grindDecode (ts j)) = p'.proof.1.ipaRounds := by
    funext j
    calc
      grindDecode (ts j) = grindDecode (algebraicFullPrefixes init p' j) :=
        congrArg grindDecode (by simpa using (hts j).symm)
      _ = p'.proof.1.ipaRounds j := (hdecode p' j).symm
  have hc : p'.proof.1.ipaC = c := congrArg Prod.fst hfinal
  have hf : p'.proof.1.ipaF = f := congrArg Prod.snd hfinal
  rw [hrounds, ← hc, ← hf, ← hPwhole cs]
  exact hacc

/-- Rewrite a certificate onto the canonical augmented basis of the deployed AGM instance. -/
def AlgebraicDForkCert.toCanonicalBasis {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (cert : AlgebraicDForkCert (F := Fp) basis shape.k) :
    AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k := by
  exact Eq.mpr (congrArg (fun b => AlgebraicDForkCert (F := Fp) b shape.k)
    (augmentedBasis_ursOfAugmentedBasis shape.k basis)) cert

/-- Transporting an algebraic certificate across an equality of basis functions leaves its
ordinary certificate unchanged. -/
theorem AlgebraicDForkCert.toDForkCert_eq_mpr_basis {shape : Shape}
    {basis basis' : AugmentedIndex (2 ^ shape.k) → VestaG} (h : basis' = basis)
    (cert : AlgebraicDForkCert (F := Fp) basis shape.k) :
    (Eq.mpr (congrArg (fun b => AlgebraicDForkCert (F := Fp) b shape.k) h) cert).toDForkCert =
      cert.toDForkCert := by
  subst basis'
  rfl

/-- Changing only the type-level name of the augmented basis does not change the erased tree. -/
theorem AlgebraicDForkCert.toCanonicalBasis_toDForkCert {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (cert : AlgebraicDForkCert (F := Fp) basis shape.k) :
    cert.toCanonicalBasis.toDForkCert = cert.toDForkCert := by
  exact AlgebraicDForkCert.toDForkCert_eq_mpr_basis
    (augmentedBasis_ursOfAugmentedBasis shape.k basis) cert

/-- Transport certificate validity to the canonical basis used by the deployed AGM instance. -/
theorem algebraicForkCertAttempt_valid_canonical {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk instanceCommitment))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (coins : RecursiveForkCoins Fp shape.k)
    (cert : AlgebraicDForkCert (F := Fp) basis shape.k)
    (hout : (algebraicForkCertAttempt basis vk instanceCommitment init A O coins).output = some cert) :
    let p := A.run O
    let ν : Fin 11 → Fp := fun i => O (algebraicFullPrefixesPre init p i)
    let urs := ursOfAugmentedBasis shape.k basis
    DeployedForkValid urs.g (evalVector shape.k (ν 7)) urs.u urs.w (ν 10)
      (commit urs
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • urs.u +
        (p.multiBlind ν + ν 9 * p.sBlind) • urs.w)
      cert.toCanonicalBasis.toDForkCert := by
  rw [AlgebraicDForkCert.toCanonicalBasis_toDForkCert]
  exact algebraicForkCertAttempt_valid basis vk instanceCommitment init A O coins cert hout

/-- Package one checked certificate with the algebraic data from its root FS run. -/
def deployedAlgebraicInstanceOfCert {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert) :
    DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis :=
  { b := evalVector shape.k (ν 7)
    v := multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))
    ξ := ν 9
    z := ν 10
    vU := p.multiU ν + ν 9 * p.sU
    blind := p.multiBlind ν + ν 9 * p.sBlind
    aMulti := p.aMulti ν
    aDep := adjustedWitness (p.aMulti ν) p.s
      (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)
    s := p.s
    cert := cert
    hz := hz
    hb0 := evalVector_zero shape.k (ν 7)
    hP := commit_adjustedWitness (ursOfAugmentedBasis shape.k basis) (p.aMulti ν) p.s
      (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)
    hvalid := hvalid }

/-- Every checked mismatch instance yields an explicit relation. -/
theorem deployedAlgebraicInstanceOfCert_runRelation_isSome
    {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (hmm : innerProduct (p.aMulti ν) (evalVector shape.k (ν 7)) ≠
      multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0)) +
        (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU) -
        ν 9 * innerProduct p.s (evalVector shape.k (ν 7))) :
    (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).runRelation.isSome :=
  DeployedAlgebraicForkingInstance.runRelation_isSome_of_mismatch
    (deployedAlgebraicInstanceOfCert p ν cert hz hvalid) hmm

/-- Compute a deployed AGM instance from one Fiat–Shamir oracle table and extractor coins.
Failure to find a valid tree, or `z = 0`, returns `none`. -/
def computedDeployedAlgebraicInstance {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk instanceCommitment))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (coins : RecursiveForkCoins Fp shape.k) :
    RecursiveForkAttempt
      (DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis) := by
  let urs := ursOfAugmentedBasis shape.k basis
  let p := A.run O
  let ν : Fin 11 → Fp := fun i => O (algebraicFullPrefixesPre init p i)
  let certAttempt := algebraicForkCertAttempt basis vk instanceCommitment init A O coins
  match hcert : certAttempt.output with
  | none => exact { output := none, runs := certAttempt.runs }
  | some cert =>
    if hz : ν 10 ≠ 0 then
      let canonicalCert := cert.toCanonicalBasis
      let b := evalVector shape.k (ν 7)
      let v := multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))
      let aDep := adjustedWitness (p.aMulti ν) p.s v (ν 9)
      let vU := p.multiU ν + ν 9 * p.sU
      let blind := p.multiBlind ν + ν 9 * p.sBlind
      have hvalid : DeployedForkValid urs.g b urs.u urs.w (ν 10)
          (commit urs aDep + vU • urs.u + blind • urs.w)
          canonicalCert.toDForkCert := by
        have hcert' : (algebraicForkCertAttempt basis vk instanceCommitment init A O coins).output = some cert := by
          simpa only [certAttempt] using hcert
        exact algebraicForkCertAttempt_valid_canonical basis vk instanceCommitment init A O coins cert hcert'
      exact
        { output := some (deployedAlgebraicInstanceOfCert p ν canonicalCert hz hvalid)
          runs := certAttempt.runs }
    else
      exact { output := none, runs := certAttempt.runs }

/-- The computed producer on the finite tape used by the probability experiment. -/
def computedDeployedAlgebraicInstanceFromTape {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk instanceCommitment))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (tape : RecursiveForkTape Fp shape.k) :
    RecursiveForkAttempt
      (DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis) :=
  computedDeployedAlgebraicInstance basis vk instanceCommitment init A O tape.toCoins

/-- Accepting oracle tables on which the certified operational producer returns no AGM instance. -/
noncomputable def computedAlgebraicInstanceFailureSet {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk instanceCommitment))
    (tape : RecursiveForkTape Fp shape.k) :
    Set (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) :=
  {O | fsWinsFull A (fullAlgebraicAcceptZ basis vk instanceCommitment)
      (algebraicFullPrefixesPre init) (algebraicFullPrefixes init) O ∧
    ¬ (computedDeployedAlgebraicInstanceFromTape basis vk instanceCommitment init A O tape).output.isSome}

/-- On an accepting run, failure of the checked instance producer implies failure of the raw
certificate producer. -/
theorem computedAlgebraicInstanceFailureSet_subset_certFailure {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk instanceCommitment))
    (tape : RecursiveForkTape Fp shape.k) :
    computedAlgebraicInstanceFailureSet basis vk instanceCommitment init A tape ⊆
      algebraicForkCertFailureSet basis vk instanceCommitment init A tape.toCoins := by
  intro O hfail
  refine ⟨hfail.1, ?_⟩
  intro hsome
  obtain ⟨cert, hcert⟩ := Option.isSome_iff_exists.mp hsome
  apply hfail.2
  unfold computedDeployedAlgebraicInstanceFromTape computedDeployedAlgebraicInstance
  dsimp only
  split
  · rename_i hnone
    rw [hnone] at hcert
    simp at hcert
  · rename_i cert' hcert'
    have hz : O (algebraicFullPrefixesPre init (A.run O) 10) ≠ 0 := hfail.1.2
    simp [hz]

/-- The executable, validity-certified producer loses no more probability than the recursive
certificate extractor itself. -/
theorem computedAlgebraicInstanceFailure_measure_le {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk instanceCommitment))
    (tape : RecursiveForkTape Fp shape.k) {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
        (computedAlgebraicInstanceFailureSet basis vk instanceCommitment init A tape)
      ≤ (Q + shape.k) * (3 / Fintype.card Fp) := by
  refine le_trans (MeasureTheory.measure_mono
    (computedAlgebraicInstanceFailureSet_subset_certFailure basis vk instanceCommitment init A tape)) ?_
  exact algebraicForkCertFailure_measure_le basis vk instanceCommitment init A tape hQ

/-- A computed binding-attack instance always returns an explicit relation. -/
theorem computedDeployedAlgebraicInstance_runRelation_isSome
    {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk instanceCommitment))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (coins : RecursiveForkCoins Fp shape.k)
    {x : DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis}
    (hwin : fsWinsFull A (fullAlgebraicBindingAttack basis vk instanceCommitment)
      (algebraicFullPrefixesPre init) (algebraicFullPrefixes init) O)
    (hinst : (computedDeployedAlgebraicInstance basis vk instanceCommitment init A O coins).output = some x) :
    x.runRelation.isSome := by
  rw [fsWinsFull] at hwin
  unfold computedDeployedAlgebraicInstance at hinst
  dsimp only at hinst
  split at hinst
  · simp at hinst
  · rename_i cert hcert
    split at hinst
    · rename_i hz
      injection hinst with hx
      subst x
      apply deployedAlgebraicInstanceOfCert_runRelation_isSome
      exact hwin.2
    · simp at hinst

/-- Tape-form specialization of `computedDeployedAlgebraicInstance_runRelation_isSome`. -/
theorem computedDeployedAlgebraicInstanceFromTape_runRelation_isSome
    {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk instanceCommitment))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (tape : RecursiveForkTape Fp shape.k)
    {x : DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis}
    (hwin : fsWinsFull A (fullAlgebraicBindingAttack basis vk instanceCommitment)
      (algebraicFullPrefixesPre init) (algebraicFullPrefixes init) O)
    (hinst : (computedDeployedAlgebraicInstanceFromTape basis vk instanceCommitment init A O tape).output = some x) :
    x.runRelation.isSome :=
  computedDeployedAlgebraicInstance_runRelation_isSome basis vk instanceCommitment init A O tape.toCoins hwin hinst

/-! ## Executable knowledge soundness

`runToSnark` returns `S ⊕' relation` under explicit circuit and encoding hypotheses. -/

/-- Turn one computed instance into the circuit statement `S` or an explicit relation. -/
def DeployedAlgebraicForkingInstance.runToSnark {k : ℕ}
    {basis : AugmentedIndex (2 ^ k) → VestaG}
    (x : DeployedAlgebraicForkingInstance (G := VestaG) k basis)
    {circuitSat : (Fin (2 ^ k) → Fp) → Prop}
    (hcirc : ∀ o : x.Opening, x.run = PSum.inl o → circuitSat o.1)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation (ursOfAugmentedBasis k basis)
        (commit (ursOfAugmentedBasis k basis) x.aMulti) x.b
        (x.v + x.z⁻¹ * x.vU - x.ξ * innerProduct x.s x.b) circuitSat a → S) :
    S ⊕' AlgebraicRelationWitness (F := Fp) basis :=
  match h : x.run with
  | PSum.inl opening => PSum.inl (hencodes opening.1 ⟨opening.2, hcirc opening h⟩)
  | PSum.inr rel => PSum.inr rel

/-! ## Computed basis-indexed producer -/

/-- A basis-indexed family with one common transcript prefix, so every basis uses the same extractor
coin type. -/
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

/-- Independent random-oracle and recursive-extractor coins. -/
abbrev Coins (family : ComputedAlgebraicFSFamily shape) :=
  (BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) ×
    RecursiveForkTape Fp shape.k

/-- Run the computed FS-to-AGM producer on one basis and one set of extractor coins. -/
def instanceAttempt (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (coins : family.Coins) :
    RecursiveForkAttempt
      (DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis) :=
  computedDeployedAlgebraicInstanceFromTape basis (family.vk basis) (family.instanceCommitment basis) family.init
    (family.adversary basis) coins.1 coins.2

/-- Run the produced instance and return its explicit relation. `runRelation` handles both the
kernel relation branch and a clean-opening commitment collision. -/
def relationFinder (family : ComputedAlgebraicFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis coins =>
    match (family.instanceAttempt basis coins).output with
    | none => none
    | some x => x.runRelation

/-- Return only the direct relation branch of the computed run. -/
def snarkRelationFinder (family : ComputedAlgebraicFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis coins =>
    match (family.instanceAttempt basis coins).output with
    | none => none
    | some x =>
      match x.run with
      | PSum.inr rel => some rel
      | PSum.inl _ => none

/-- Bound the direct relation branch by the textbook-DL advantage plus `1/|Fp|`. -/
theorem snarkRelation_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        (relSetWithCoins B family.snarkRelationFinder)
      ≤ (bound + 1 / Fintype.card Fp) :=
  relationWithCoins_prob_le_of_textbookDL B family.snarkRelationFinder hDL

/-- The modeled deployed binding-attack event for one oracle table. -/
def bindingWin (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (O : family.Coins) : Prop :=
  fsWinsFull (family.adversary basis) (fullAlgebraicBindingAttack basis (family.vk basis) (family.instanceCommitment basis))
    (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) O.1

/-- Binding runs on which the operational producer returns no instance. -/
def failedBinding (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) : Set family.Coins :=
  {coins | family.bindingWin basis coins ∧
    ¬ (family.instanceAttempt basis coins).output.isSome}

/-- For one sampled basis, failed binding extraction is bounded by the recursive query loss and
the adaptive `z = 0` slice. -/
theorem failedBinding_measure_le (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure (family.failedBinding basis)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) := by
  let acceptFailure : Set family.Coins := {coins |
    fsWinsFull (family.adversary basis) (fullAlgebraicAcceptZ basis (family.vk basis) (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 ∧
    ¬ (family.instanceAttempt basis coins).output.isSome}
  let zeroFailure : Set family.Coins := {coins |
    family.bindingWin basis coins ∧
      coins.1 (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run coins.1) 10) = 0}
  have haccept : (PMF.uniformOfFintype family.Coins).toOuterMeasure acceptFailure ≤
      (family.Q + shape.k) * (3 / Fintype.card Fp) := by
    apply uniformOfFintype_prod_fiber_bound
      (fun tape => computedAlgebraicInstanceFailureSet basis (family.vk basis) (family.instanceCommitment basis) family.init
        (family.adversary basis) tape)
    intro tape
    exact computedAlgebraicInstanceFailure_measure_le basis (family.vk basis) (family.instanceCommitment basis) family.init
      (family.adversary basis) tape (family.queryBound basis)
  have hzero : (PMF.uniformOfFintype family.Coins).toOuterMeasure zeroFailure ≤
      (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) := by
    apply uniformOfFintype_prod_fiber_bound
      (fun _tape : RecursiveForkTape Fp shape.k =>
        {O | fsWinsFull (family.adversary basis)
            (fullAlgebraicBindingAttack basis (family.vk basis) (family.instanceCommitment basis))
            (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) O ∧
          O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 10) = 0})
    intro _
    exact fsAdvantageFull_zero_slice_le (family.adversary basis)
      (fullAlgebraicBindingAttack basis (family.vk basis) (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) 10
      (family.queryBound basis)
  have hsub : family.failedBinding basis ⊆ acceptFailure ∪ zeroFailure := by
    intro coins hfail
    by_cases hz : coins.1 (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run coins.1) 10) = 0
    · exact Or.inr ⟨hfail.1, hz⟩
    · refine Or.inl ⟨?_, hfail.2⟩
      exact ⟨hfail.1.1, hz⟩
  refine le_trans (MeasureTheory.measure_mono hsub)
    (le_trans (MeasureTheory.measure_union_le _ _) ?_)
  exact add_le_add haccept hzero

/-- The relation finder retains every instance returned on a binding-attack run. -/
theorem relationFinder_isSome_of_bindingWin
    (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (coins : family.Coins)
    (hwin : family.bindingWin basis coins)
    (hsome : (family.instanceAttempt basis coins).output.isSome) :
    (family.relationFinder basis coins).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
  have hrel := computedDeployedAlgebraicInstanceFromTape_runRelation_isSome basis
    (family.vk basis) (family.instanceCommitment basis) family.init (family.adversary basis) coins.1 coins.2 hwin hx
  unfold relationFinder
  rw [hx]
  exact hrel

/-- Basis/coin pairs on which the modeled binding attack occurs and the recursive extractor returns an
instance. -/
noncomputable def successfulBindingSet
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) :
    Finset ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins) := by
  classical
  exact Finset.univ.filter fun p =>
    family.bindingWin (scalarBasis B p.1) p.2 ∧
      (family.instanceAttempt (scalarBasis B p.1) p.2).output.isSome

/-- All modeled binding runs, before extraction success is required. -/
noncomputable def bindingSet
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) :
    Finset ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins) := by
  classical
  exact Finset.univ.filter fun p => family.bindingWin (scalarBasis B p.1) p.2

/-- The binding event on an explicit augmented basis and extractor coins. -/
def bindingEvent (family : ComputedAlgebraicFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) :=
  {p | family.bindingWin p.1 p.2}

/-- Modeled binding runs lost by the executable producer. -/
noncomputable def failedBindingSet
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) :
    Finset ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins) := by
  classical
  exact Finset.univ.filter fun p => p.2 ∈ family.failedBinding (scalarBasis B p.1)

/-- Averaging over the sampled basis does not increase the uniform extractor-loss bound. -/
theorem failedBindingSet_prob_le
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        (failedBindingSet B family)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) := by
  have hset : (↑(failedBindingSet B family) :
      Set ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)) =
      {p | p.2 ∈ family.failedBinding (scalarBasis B p.1)} := by
    ext p
    simp only [failedBindingSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and, Set.mem_setOf_eq]
  rw [hset]
  apply uniformOfFintype_prod_fiber_bound_right
    (β := (family.Q + shape.k) * (3 / Fintype.card Fp) +
      (family.Q + 1 : ℕ) * (1 / Fintype.card Fp))
    (fun coeffs : AugmentedIndex (2 ^ shape.k) → Fp =>
      family.failedBinding (scalarBasis B coeffs))
  intro coeffs
  exact failedBinding_measure_le (shape := shape) family (scalarBasis B coeffs)

/-- Every binding run either produces an instance or lies in the explicitly bounded failure set. -/
theorem bindingSet_subset_success_union_failure
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) :
    (↑(bindingSet B family) :
        Set ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)) ⊆
      (↑(successfulBindingSet B family) :
          Set ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)) ∪
      (↑(failedBindingSet B family) :
          Set ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)) := by
  intro p hp
  simp only [bindingSet, successfulBindingSet, failedBindingSet, Finset.mem_coe,
    Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_union] at hp ⊢
  by_cases hsome : (family.instanceAttempt (scalarBasis B p.1) p.2).output.isSome
  · exact Or.inl ⟨hp, hsome⟩
  · exact Or.inr ⟨hp, hsome⟩

/-- Every successfully extracted binding run is a relation-producing run of the computed finder. -/
theorem successfulBindingSet_subset_relSet
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) :
    successfulBindingSet B family ⊆ relSetWithCoins B family.relationFinder := by
  intro p hp
  simp only [successfulBindingSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  simp only [relSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and]
  exact family.relationFinder_isSome_of_bindingWin (scalarBasis B p.1) p.2 hp.1 hp.2

/-- Plain-DL hardness bounds the probability of modeled binding runs on which the executable extractor
returns an AGM instance. -/
theorem successfulBinding_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.relationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        (successfulBindingSet B family)
      ≤ (bound + 1 / Fintype.card Fp) := by
  refine le_trans (MeasureTheory.measure_mono (successfulBindingSet_subset_relSet B family)) ?_
  exact relationWithCoins_prob_le_of_textbookDL B family.relationFinder hDL

/-- Composed probability bound: the modeled deployed binding event is at most the
recursive query loss, the adaptive `z = 0` loss, and the programmed-basis plain-DL term. -/
theorem binding_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.relationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        (bindingSet B family)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  refine le_trans (MeasureTheory.measure_mono
    (bindingSet_subset_success_union_failure B family)) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  have hsuccess := successfulBinding_prob_le_of_textbookDL B family hDL
  have hfailure := failedBindingSet_prob_le B family
  exact add_le_add hsuccess hfailure |>.trans_eq (by ac_rfl)

/-- Transfer the binding experiment across a uniform-URS basis identification. -/
theorem binding_prob_eq_of_uniformURS {Ω : Type*} (setup : PMF Ω)
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape)
    (basisOf : Ω → AugmentedIndex (2 ^ shape.k) → VestaG)
    (hURS : OrchardUniformURSIdentification setup shape.k B basisOf) :
    (independentProductPMF setup (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' family.bindingEvent) =
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        (bindingSet B family) := by
  let coinPMF := PMF.uniformOfFintype family.Coins
  have hprod :
      (independentProductPMF setup coinPMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)) coinPMF).map
            (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) coinPMF :=
        independentProductPMF_map_left setup coinPMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)).map (scalarBasis B))
          coinPMF := congrArg (fun p => independentProductPMF p coinPMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)) coinPMF
        (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) =>
      p.toOuterMeasure family.bindingEvent) hprod
  change ((independentProductPMF setup coinPMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure family.bindingEvent =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)) coinPMF).map
        (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure family.bindingEvent at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)) coinPMF).toOuterMeasure
          ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' family.bindingEvent) := hmeasure
    _ = (PMF.uniformOfFintype
          ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
          (bindingSet B family) := by
      rw [independentProductPMF_uniform]
      congr 1
      ext p
      simp only [Set.mem_preimage, bindingEvent, Set.mem_setOf_eq, bindingSet,
        Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The composed binding bound under an explicit uniform-URS setup distribution. -/
theorem binding_prob_le_of_uniformURS_textbookDL {Ω : Type*} (setup : PMF Ω)
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape)
    (basisOf : Ω → AugmentedIndex (2 ^ shape.k) → VestaG)
    {bound : ℝ≥0∞} (hURS : OrchardUniformURSIdentification setup shape.k B basisOf)
    (hDL : TextbookDLWithCoinsAdvantageLE B family.relationFinder bound) :
    (independentProductPMF setup (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' family.bindingEvent)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  rw [binding_prob_eq_of_uniformURS setup B family basisOf hURS]
  exact binding_prob_le_of_textbookDL B family hDL

/-- The composed binding bound in the uniform generator-random-oracle setup model. -/
theorem binding_prob_le_of_generatorRO_textbookDL
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.relationFinder bound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' family.bindingEvent)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) :=
  binding_prob_le_of_uniformURS_textbookDL (orchardGeneratorROSetup query) B family
    (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery) hDL

/-! ## Clean-opening probability

Charge missing clean openings to extraction failure or a direct relation. -/

/-- A produced instance whose run is a clean IPA opening — the branch on which `runToSnark` returns
`S`. Its negation is a missing instance or the direct-relation branch. -/
def hasCleanOpening (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (coins : family.Coins) : Prop :=
  ∃ x, (family.instanceAttempt basis coins).output = some x ∧ ∃ o, x.run = PSum.inl o

/-- Nonzero-challenge accepting runs on which the producer returns no instance. -/
def acceptExtractionFailure (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) : Set family.Coins :=
  {coins | fsWinsFull (family.adversary basis) (fullAlgebraicAcceptZ basis (family.vk basis) (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 ∧
    ¬ (family.instanceAttempt basis coins).output.isSome}

/-- Accepting extractor failure on one basis is bounded by the recursive query loss. -/
theorem acceptExtractionFailure_measure_le (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure (family.acceptExtractionFailure basis)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) := by
  apply uniformOfFintype_prod_fiber_bound
    (fun tape => computedAlgebraicInstanceFailureSet basis (family.vk basis) (family.instanceCommitment basis) family.init
      (family.adversary basis) tape)
  intro tape
  exact computedAlgebraicInstanceFailure_measure_le basis (family.vk basis) (family.instanceCommitment basis) family.init
    (family.adversary basis) tape (family.queryBound basis)

/-- Non-relation failures: no instance on a `z ≠ 0` accepting run, or an accepting `z = 0` run. -/
def snarkNonRelationFailure (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) : Set family.Coins :=
  family.acceptExtractionFailure basis ∪
    {coins | fsWinsFull (family.adversary basis) (fullAlgebraicAccept basis (family.vk basis) (family.instanceCommitment basis))
        (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 ∧
      coins.1 (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run coins.1) 10) = 0}

/-- The non-relation failure on one basis is bounded by the recursive query loss and the `z = 0`
slice. -/
theorem snarkNonRelationFailure_measure_le (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure (family.snarkNonRelationFailure basis)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) := by
  refine le_trans (MeasureTheory.measure_union_le _ _)
    (add_le_add (family.acceptExtractionFailure_measure_le basis) ?_)
  apply uniformOfFintype_prod_fiber_bound
    (fun _tape : RecursiveForkTape Fp shape.k =>
      {O | fsWinsFull (family.adversary basis) (fullAlgebraicAccept basis (family.vk basis) (family.instanceCommitment basis))
          (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) O ∧
        O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 10) = 0})
  intro _tape
  exact fsAdvantageFull_zero_slice_le (family.adversary basis)
    (fullAlgebraicAccept basis (family.vk basis) (family.instanceCommitment basis))
    (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) 10
    (family.queryBound basis)

/-- On `z ≠ 0` accepting runs, bound failure to return a clean opening by
`(Q+k)·3/|Fp| + DLadv + 1/|Fp|`. -/
theorem snarkFailure_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        {p | fsWinsFull (family.adversary (scalarBasis B p.1))
              (fullAlgebraicAcceptZ (scalarBasis B p.1) (family.vk (scalarBasis B p.1)) (family.instanceCommitment (scalarBasis B p.1)))
              (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) p.2.1 ∧
            ¬ family.hasCleanOpening (scalarBasis B p.1) p.2}
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  refine le_trans (MeasureTheory.measure_mono
    (show {p : (AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins |
        fsWinsFull (family.adversary (scalarBasis B p.1))
          (fullAlgebraicAcceptZ (scalarBasis B p.1) (family.vk (scalarBasis B p.1)) (family.instanceCommitment (scalarBasis B p.1)))
          (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) p.2.1 ∧
        ¬ family.hasCleanOpening (scalarBasis B p.1) p.2} ⊆
      {p | p.2 ∈ family.acceptExtractionFailure (scalarBasis B p.1)} ∪
      (↑(relSetWithCoins B family.snarkRelationFinder) :
        Set ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)) from ?_))
    (le_trans (MeasureTheory.measure_union_le _ _) ?_)
  · intro p hp
    obtain ⟨hacc, hnoclean⟩ := hp
    by_cases hsome : (family.instanceAttempt (scalarBasis B p.1) p.2).output.isSome
    · refine Or.inr ?_
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
      simp only [Finset.mem_coe, relSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and]
      show (family.snarkRelationFinder (scalarBasis B p.1) p.2).isSome
      simp only [snarkRelationFinder, hx]
      cases hrun : x.run with
      | inl o => exact absurd ⟨x, hx, o, hrun⟩ hnoclean
      | inr rel => rfl
    · exact Or.inl ⟨hacc, hsome⟩
  · refine add_le_add ?_ (snarkRelation_prob_le_of_textbookDL B family hDL)
    apply uniformOfFintype_prod_fiber_bound_right
      (fun coeffs : AugmentedIndex (2 ^ shape.k) → Fp =>
        family.acceptExtractionFailure (scalarBasis B coeffs))
    intro coeffs
    exact family.acceptExtractionFailure_measure_le (scalarBasis B coeffs)

/-- Full-acceptance clean-opening bound, adding the `(Q+1)/|Fp|` zero-challenge slice. -/
theorem snarkFailure_prob_le_of_textbookDL_full
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        {p | fsWinsFull (family.adversary (scalarBasis B p.1))
              (fullAlgebraicAccept (scalarBasis B p.1) (family.vk (scalarBasis B p.1)) (family.instanceCommitment (scalarBasis B p.1)))
              (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) p.2.1 ∧
            ¬ family.hasCleanOpening (scalarBasis B p.1) p.2}
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  refine le_trans (MeasureTheory.measure_mono
    (show {p : (AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins |
        fsWinsFull (family.adversary (scalarBasis B p.1))
          (fullAlgebraicAccept (scalarBasis B p.1) (family.vk (scalarBasis B p.1)) (family.instanceCommitment (scalarBasis B p.1)))
          (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) p.2.1 ∧
        ¬ family.hasCleanOpening (scalarBasis B p.1) p.2} ⊆
      {p | fsWinsFull (family.adversary (scalarBasis B p.1))
            (fullAlgebraicAcceptZ (scalarBasis B p.1) (family.vk (scalarBasis B p.1)) (family.instanceCommitment (scalarBasis B p.1)))
            (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) p.2.1 ∧
          ¬ family.hasCleanOpening (scalarBasis B p.1) p.2} ∪
      {p | fsWinsFull (family.adversary (scalarBasis B p.1))
            (fullAlgebraicAccept (scalarBasis B p.1) (family.vk (scalarBasis B p.1)) (family.instanceCommitment (scalarBasis B p.1)))
            (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) p.2.1 ∧
          p.2.1 (algebraicFullPrefixesPre family.init
            ((family.adversary (scalarBasis B p.1)).run p.2.1) 10) = 0} from ?_))
    (le_trans (MeasureTheory.measure_union_le _ _) ?_)
  · intro p hp
    obtain ⟨hacc, hnoclean⟩ := hp
    by_cases hz : p.2.1 (algebraicFullPrefixesPre family.init
        ((family.adversary (scalarBasis B p.1)).run p.2.1) 10) = 0
    · exact Or.inr ⟨hacc, hz⟩
    · exact Or.inl ⟨⟨hacc, hz⟩, hnoclean⟩
  · have hzero : (PMF.uniformOfFintype
          ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
          {p | fsWinsFull (family.adversary (scalarBasis B p.1))
                (fullAlgebraicAccept (scalarBasis B p.1) (family.vk (scalarBasis B p.1)) (family.instanceCommitment (scalarBasis B p.1)))
                (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) p.2.1 ∧
              p.2.1 (algebraicFullPrefixesPre family.init
                ((family.adversary (scalarBasis B p.1)).run p.2.1) 10) = 0}
        ≤ (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) := by
      apply uniformOfFintype_prod_fiber_bound_right
        (fun coeffs : AugmentedIndex (2 ^ shape.k) → Fp =>
          {coins : family.Coins |
            fsWinsFull (family.adversary (scalarBasis B coeffs))
              (fullAlgebraicAccept (scalarBasis B coeffs) (family.vk (scalarBasis B coeffs)) (family.instanceCommitment (scalarBasis B coeffs)))
              (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 ∧
            coins.1 (algebraicFullPrefixesPre family.init
              ((family.adversary (scalarBasis B coeffs)).run coins.1) 10) = 0})
      intro coeffs
      apply uniformOfFintype_prod_fiber_bound
        (fun _tape : RecursiveForkTape Fp shape.k =>
          {O | fsWinsFull (family.adversary (scalarBasis B coeffs))
              (fullAlgebraicAccept (scalarBasis B coeffs) (family.vk (scalarBasis B coeffs)) (family.instanceCommitment (scalarBasis B coeffs)))
              (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) O ∧
            O (algebraicFullPrefixesPre family.init
              ((family.adversary (scalarBasis B coeffs)).run O) 10) = 0})
      intro _tape
      exact fsAdvantageFull_zero_slice_le (family.adversary (scalarBasis B coeffs))
        (fullAlgebraicAccept (scalarBasis B coeffs) (family.vk (scalarBasis B coeffs)) (family.instanceCommitment (scalarBasis B coeffs)))
        (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) 10
        (family.queryBound (scalarBasis B coeffs))
    exact (add_le_add (snarkFailure_prob_le_of_textbookDL B family hDL) hzero).trans_eq
      (by ac_rfl)

/-- The full-acceptance clean-opening failure event on an explicit augmented basis and extractor
coins: plain deployed acceptance with no clean opening. -/
def snarkFailureEvent (family : ComputedAlgebraicFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) :=
  {q | fsWinsFull (family.adversary q.1) (fullAlgebraicAccept q.1 (family.vk q.1) (family.instanceCommitment q.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2.1 ∧
    ¬ family.hasCleanOpening q.1 q.2}

/-- Transfer the SNARK-failure experiment across a uniform-URS basis identification. -/
theorem snarkFailure_prob_eq_of_uniformURS {Ω : Type*} (setup : PMF Ω)
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape)
    (basisOf : Ω → AugmentedIndex (2 ^ shape.k) → VestaG)
    (hURS : OrchardUniformURSIdentification setup shape.k B basisOf) :
    (independentProductPMF setup (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' family.snarkFailureEvent) =
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' family.snarkFailureEvent) := by
  let coinPMF := PMF.uniformOfFintype family.Coins
  have hprod :
      (independentProductPMF setup coinPMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)) coinPMF).map
            (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) coinPMF :=
        independentProductPMF_map_left setup coinPMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)).map (scalarBasis B))
          coinPMF := congrArg (fun p => independentProductPMF p coinPMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)) coinPMF
        (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) =>
      p.toOuterMeasure family.snarkFailureEvent) hprod
  change ((independentProductPMF setup coinPMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure family.snarkFailureEvent =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)) coinPMF).map
        (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure family.snarkFailureEvent at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  rw [hmeasure, independentProductPMF_uniform]

/-- The full-acceptance clean-opening bound under an explicit uniform-URS setup. -/
theorem snarkFailure_prob_le_of_uniformURS_textbookDL {Ω : Type*} (setup : PMF Ω)
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape)
    (basisOf : Ω → AugmentedIndex (2 ^ shape.k) → VestaG)
    {bound : ℝ≥0∞} (hURS : OrchardUniformURSIdentification setup shape.k B basisOf)
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound) :
    (independentProductPMF setup (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' family.snarkFailureEvent)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  rw [snarkFailure_prob_eq_of_uniformURS setup B family basisOf hURS]
  exact snarkFailure_prob_le_of_textbookDL_full B family hDL

/-- Generator-RO form of the full-acceptance clean-opening bound. -/
theorem snarkFailure_prob_le_of_generatorRO_textbookDL
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' family.snarkFailureEvent)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) :=
  snarkFailure_prob_le_of_uniformURS_textbookDL (orchardGeneratorROSetup query) B family
    (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery) hDL

/-! ### Discrete-log hardness and runtime

Probability bounds need no runtime premise. The DL-hardness endpoint still needs a polynomial AFK
black-box call bound; adversary PPT time remains external. -/

/-- The extractor makes at most `R` expected black-box adversary calls for every basis. -/
def ReductionEfficient (family : ComputedAlgebraicFSFamily shape) (R : ℕ) : Prop :=
  ∀ basis : AugmentedIndex (2 ^ shape.k) → VestaG,
    ∑ coins : family.Coins, (family.instanceAttempt basis coins).runs
      ≤ R * Fintype.card family.Coins

/-- Every fixed family has a finite call bound; this is not a uniform asymptotic bound. -/
theorem reductionEfficient_exists (family : ComputedAlgebraicFSFamily shape) :
    ∃ R, family.ReductionEfficient R := by
  refine ⟨Finset.univ.sup fun basis => ∑ coins : family.Coins,
      (family.instanceAttempt basis coins).runs, fun basis => ?_⟩
  calc ∑ coins : family.Coins, (family.instanceAttempt basis coins).runs
      ≤ Finset.univ.sup fun b => ∑ coins : family.Coins,
          (family.instanceAttempt b coins).runs :=
        Finset.le_sup (f := fun b => ∑ coins : family.Coins,
          (family.instanceAttempt b coins).runs) (Finset.mem_univ basis)
    _ ≤ (Finset.univ.sup fun b => ∑ coins : family.Coins,
          (family.instanceAttempt b coins).runs) * Fintype.card family.Coins :=
        Nat.le_mul_of_pos_right _ Fintype.card_pos

/-- `instanceAttempt.runs` is the recursive extractor's adversary-call count. -/
theorem instanceAttempt_runs_eq (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (coins : family.Coins) :
    (family.instanceAttempt basis coins).runs
      = (algebraicForkCertAttempt basis (family.vk basis) (family.instanceCommitment basis) family.init
          (family.adversary basis) coins.1 coins.2.toCoins).runs := by
  unfold instanceAttempt computedDeployedAlgebraicInstanceFromTape
  simp only [computedDeployedAlgebraicInstance]
  split
  · rfl
  · split <;> rfl

/-- The unconditional call bound `(2·|F|+1)^k` is not field-independent polynomial AFK. -/
theorem reductionEfficient_exponential (family : ComputedAlgebraicFSFamily shape) :
    family.ReductionEfficient ((2 * Fintype.card Fp + 1) ^ shape.k) := by
  intro basis
  rw [Finset.sum_congr rfl (fun coins _ => family.instanceAttempt_runs_eq basis coins)]
  exact recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional basis shape.k
    (family.adversary basis) (algebraicFullPrefixes family.init) (fun p => p.rounds)
    (fun p => (p.proof.1.ipaC, p.proof.1.ipaF))
    (algebraicTableAcceptZ basis (family.vk basis) (family.instanceCommitment basis) family.init) _

/-- Textbook DL hardness at advantage `ε`, as it applies to *one* reduction family with expected
call bound `R`: if the family's extractor meets the call bound, its two derived solvers have
advantage at most `ε`.  Stated per family, not `∀`-quantified over families: a family's adversary
is an arbitrary Lean function whose own running time is not encoded, so a family-universal form
would range over computationally unbounded solvers and could not be soundly assumed at
cryptographic `ε`.  For a PPT family this predicate is what standard DL hardness supplies;
PPT-ness of the family remains the external premise. -/
def DiscreteLogRelationHardFor (B : VestaG) (family : ComputedAlgebraicFSFamily shape)
    (R : ℕ) (ε : ℝ≥0∞) : Prop :=
  family.ReductionEfficient R →
    TextbookDLWithCoinsAdvantageLE B family.relationFinder ε ∧
    TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder ε

/-- Under DL hardness for this family and call bound `R`, bound clean-opening failure by the
recursive losses and `ε + 1/|Fp|`; a polynomial AFK instantiation of `R` remains open. -/
theorem knowledgeSoundness_under_DL
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) {R : ℕ} {ε : ℝ≥0∞}
    (hHard : DiscreteLogRelationHardFor B family R ε)
    (hEff : family.ReductionEfficient R) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        {p | fsWinsFull (family.adversary (scalarBasis B p.1))
              (fullAlgebraicAccept (scalarBasis B p.1) (family.vk (scalarBasis B p.1)) (family.instanceCommitment (scalarBasis B p.1)))
              (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) p.2.1 ∧
            ¬ family.hasCleanOpening (scalarBasis B p.1) p.2}
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (ε + 1 / Fintype.card Fp) :=
  snarkFailure_prob_le_of_textbookDL_full B family (hHard hEff).2

/-- Binding dual of `knowledgeSoundness_under_DL`. -/
theorem binding_under_DL
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) {R : ℕ} {ε : ℝ≥0∞}
    (hHard : DiscreteLogRelationHardFor B family R ε)
    (hEff : family.ReductionEfficient R) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        (bindingSet B family)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (ε + 1 / Fintype.card Fp) :=
  binding_prob_le_of_textbookDL B family (hHard hEff).1

end ComputedAlgebraicFSFamily

/-! ## Unbounded oracle domain

Bounded-query adversaries over transcript lists reduce to their finite reachable-support split.
Blake2b remains idealized; `truncateTranscript` is only the deployed bounded-transcript retraction. -/

/-- Transfer a uniform bounded-transcript binding bound to the reachable-support split. -/
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

/-! ## Randomized adversaries

Private coins form a uniform mixture of deterministic adversaries. -/

/-- A basis-indexed adversary family with independent finite private coins. -/
structure ComputedAlgebraicFSFamilyRand (shape : Shape) (R : Type*) where
  init : List (TranscriptElt Fp VestaG)
  vk : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → VerifyingKey shape Fp VestaG
  instanceCommitment : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → Fin shape.numProofs → ℕ → VestaG
  adversary : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → R → OracleComp
    (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
    (AlgebraicWfProof basis (vk basis) (instanceCommitment basis))
  Q : ℕ
  queryBound : ∀ basis r, (adversary basis r).QueryBound Q

namespace ComputedAlgebraicFSFamilyRand

variable {shape : Shape} {R : Type*}

/-- The deterministic member obtained by fixing the private coins. -/
abbrev determinize (fam : ComputedAlgebraicFSFamilyRand shape R) (r : R) :
    ComputedAlgebraicFSFamily shape :=
  { init := fam.init
    vk := fam.vk
    instanceCommitment := fam.instanceCommitment
    adversary := fun basis => fam.adversary basis r
    Q := fam.Q
    queryBound := fun basis => fam.queryBound basis r }

/-- The oracle-table and extractor-tape coins, shared by every member. -/
abbrev Coins (fam : ComputedAlgebraicFSFamilyRand shape R) :=
  (BTranscript Fp VestaG (preIpaLen shape fam.init.length 10 + 3 * shape.k) → Fp) ×
    RecursiveForkTape Fp shape.k

/-- Average the binding bound over private coins. -/
theorem binding_prob_le_of_textbookDL_rand [Fintype R] [Nonempty R]
    (B : VestaG) (fam : ComputedAlgebraicFSFamilyRand shape R) {bound : ℝ≥0∞}
    (hDL : ∀ r, TextbookDLWithCoinsAdvantageLE B (fam.determinize r).relationFinder bound) :
    (PMF.uniformOfFintype
        (((AugmentedIndex (2 ^ shape.k) → Fp) × fam.Coins) × R)).toOuterMeasure
        {p : ((AugmentedIndex (2 ^ shape.k) → Fp) × fam.Coins) × R |
          p.1 ∈ (ComputedAlgebraicFSFamily.bindingSet B (fam.determinize p.2) :
            Set ((AugmentedIndex (2 ^ shape.k) → Fp) × fam.Coins))}
      ≤ (fam.Q + shape.k) * (3 / Fintype.card Fp) +
        (fam.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  apply uniformOfFintype_prod_fiber_bound
    (fun r => (ComputedAlgebraicFSFamily.bindingSet B (fam.determinize r) :
      Set ((AugmentedIndex (2 ^ shape.k) → Fp) × fam.Coins)))
  intro r
  exact ComputedAlgebraicFSFamily.binding_prob_le_of_textbookDL B (fam.determinize r) (hDL r)

/-- Fold the adversary's private coin into one randomized DL solver. -/
def foldedRelationFinder (fam : ComputedAlgebraicFSFamilyRand shape R) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → (fam.Coins × R) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis p => (fam.determinize p.2).relationFinder basis p.1

/-- Bound averaged binding from one DL bound on the private-coin-folded solver. -/
theorem binding_prob_le_of_foldedTextbookDL_rand [Fintype R] [Nonempty R]
    (B : VestaG) (fam : ComputedAlgebraicFSFamilyRand shape R) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B fam.foldedRelationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × (fam.Coins × R))).toOuterMeasure
        {p : (AugmentedIndex (2 ^ shape.k) → Fp) × (fam.Coins × R) |
          ComputedAlgebraicFSFamily.bindingWin (fam.determinize p.2.2)
            (scalarBasis B p.1) p.2.1}
      ≤ (fam.Q + shape.k) * (3 / Fintype.card Fp) +
        (fam.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  refine le_trans (MeasureTheory.measure_mono
    (show {p : (AugmentedIndex (2 ^ shape.k) → Fp) × (fam.Coins × R) |
        ComputedAlgebraicFSFamily.bindingWin (fam.determinize p.2.2)
          (scalarBasis B p.1) p.2.1} ⊆
      {p | ComputedAlgebraicFSFamily.bindingWin (fam.determinize p.2.2)
          (scalarBasis B p.1) p.2.1 ∧
        (ComputedAlgebraicFSFamily.instanceAttempt (fam.determinize p.2.2)
          (scalarBasis B p.1) p.2.1).output.isSome} ∪
      {p | ComputedAlgebraicFSFamily.bindingWin (fam.determinize p.2.2)
          (scalarBasis B p.1) p.2.1 ∧
        ¬ (ComputedAlgebraicFSFamily.instanceAttempt (fam.determinize p.2.2)
          (scalarBasis B p.1) p.2.1).output.isSome} from ?_)) ?_
  · intro p hp
    by_cases hsome : (ComputedAlgebraicFSFamily.instanceAttempt (fam.determinize p.2.2)
        (scalarBasis B p.1) p.2.1).output.isSome
    · exact Or.inl ⟨hp, hsome⟩
    · exact Or.inr ⟨hp, hsome⟩
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  have hsucc : (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × (fam.Coins × R))).toOuterMeasure
        {p | ComputedAlgebraicFSFamily.bindingWin (fam.determinize p.2.2)
            (scalarBasis B p.1) p.2.1 ∧
          (ComputedAlgebraicFSFamily.instanceAttempt (fam.determinize p.2.2)
            (scalarBasis B p.1) p.2.1).output.isSome}
      ≤ (bound + 1 / Fintype.card Fp) := by
    refine le_trans (MeasureTheory.measure_mono ?_)
      (relationWithCoins_prob_le_of_textbookDL B fam.foldedRelationFinder hDL)
    intro p hp
    simp only [relSetWithCoins, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      foldedRelationFinder]
    exact (fam.determinize p.2.2).relationFinder_isSome_of_bindingWin
      (scalarBasis B p.1) p.2.1 hp.1 hp.2
  have hfail : (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × (fam.Coins × R))).toOuterMeasure
        {p | ComputedAlgebraicFSFamily.bindingWin (fam.determinize p.2.2)
            (scalarBasis B p.1) p.2.1 ∧
          ¬ (ComputedAlgebraicFSFamily.instanceAttempt (fam.determinize p.2.2)
            (scalarBasis B p.1) p.2.1).output.isSome}
      ≤ (fam.Q + shape.k) * (3 / Fintype.card Fp) +
        (fam.Q + 1 : ℕ) * (1 / Fintype.card Fp) := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun coeffs : AugmentedIndex (2 ^ shape.k) → Fp =>
        {cr : fam.Coins × R |
          ComputedAlgebraicFSFamily.bindingWin (fam.determinize cr.2)
            (scalarBasis B coeffs) cr.1 ∧
          ¬ (ComputedAlgebraicFSFamily.instanceAttempt (fam.determinize cr.2)
            (scalarBasis B coeffs) cr.1).output.isSome})
    intro coeffs
    apply uniformOfFintype_prod_fiber_bound
      (fun r : R => {coins : fam.Coins |
        ComputedAlgebraicFSFamily.bindingWin (fam.determinize r) (scalarBasis B coeffs) coins ∧
        ¬ (ComputedAlgebraicFSFamily.instanceAttempt (fam.determinize r)
          (scalarBasis B coeffs) coins).output.isSome})
    intro r
    exact ComputedAlgebraicFSFamily.failedBinding_measure_le (fam.determinize r)
      (scalarBasis B coeffs)
  exact (add_le_add hsucc hfail).trans_eq (by ac_rfl)

/-- Average the full-acceptance clean-opening bound over private coins. -/
theorem snarkFailure_prob_le_of_textbookDL_rand [Fintype R] [Nonempty R]
    (B : VestaG) (fam : ComputedAlgebraicFSFamilyRand shape R) {bound : ℝ≥0∞}
    (hDL : ∀ r, TextbookDLWithCoinsAdvantageLE B (fam.determinize r).snarkRelationFinder bound) :
    (PMF.uniformOfFintype
        (((AugmentedIndex (2 ^ shape.k) → Fp) × fam.Coins) × R)).toOuterMeasure
        {p : ((AugmentedIndex (2 ^ shape.k) → Fp) × fam.Coins) × R |
          fsWinsFull ((fam.determinize p.2).adversary (scalarBasis B p.1.1))
            (fullAlgebraicAccept (scalarBasis B p.1.1)
              ((fam.determinize p.2).vk (scalarBasis B p.1.1)) ((fam.determinize p.2).instanceCommitment (scalarBasis B p.1.1)))
            (algebraicFullPrefixesPre (fam.determinize p.2).init)
            (algebraicFullPrefixes (fam.determinize p.2).init) p.1.2.1 ∧
          ¬ (fam.determinize p.2).hasCleanOpening (scalarBasis B p.1.1) p.1.2}
      ≤ (fam.Q + shape.k) * (3 / Fintype.card Fp) +
        (fam.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  apply uniformOfFintype_prod_fiber_bound
    (fun r => {q : (AugmentedIndex (2 ^ shape.k) → Fp) × fam.Coins |
      fsWinsFull ((fam.determinize r).adversary (scalarBasis B q.1))
        (fullAlgebraicAccept (scalarBasis B q.1) ((fam.determinize r).vk (scalarBasis B q.1)) ((fam.determinize r).instanceCommitment (scalarBasis B q.1)))
        (algebraicFullPrefixesPre (fam.determinize r).init)
        (algebraicFullPrefixes (fam.determinize r).init) q.2.1 ∧
      ¬ (fam.determinize r).hasCleanOpening (scalarBasis B q.1) q.2})
  intro r
  exact ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL_full B
    (fam.determinize r) (hDL r)

/-- Fold the adversary's private coin into one randomized run-relation solver. -/
def foldedSnarkRelationFinder (fam : ComputedAlgebraicFSFamilyRand shape R) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → (fam.Coins × R) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis p => (fam.determinize p.2).snarkRelationFinder basis p.1

/-- Bound averaged clean-opening failure from one DL bound on the private-coin-folded solver. -/
theorem snarkFailure_prob_le_of_foldedTextbookDL_rand [Fintype R] [Nonempty R]
    (B : VestaG) (fam : ComputedAlgebraicFSFamilyRand shape R) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B fam.foldedSnarkRelationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × (fam.Coins × R))).toOuterMeasure
        {p : (AugmentedIndex (2 ^ shape.k) → Fp) × (fam.Coins × R) |
          fsWinsFull ((fam.determinize p.2.2).adversary (scalarBasis B p.1))
            (fullAlgebraicAccept (scalarBasis B p.1)
              ((fam.determinize p.2.2).vk (scalarBasis B p.1)) ((fam.determinize p.2.2).instanceCommitment (scalarBasis B p.1)))
            (algebraicFullPrefixesPre (fam.determinize p.2.2).init)
            (algebraicFullPrefixes (fam.determinize p.2.2).init) p.2.1.1 ∧
          ¬ (fam.determinize p.2.2).hasCleanOpening (scalarBasis B p.1) p.2.1}
      ≤ (fam.Q + shape.k) * (3 / Fintype.card Fp) +
        (fam.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  refine le_trans (MeasureTheory.measure_mono
    (show {p : (AugmentedIndex (2 ^ shape.k) → Fp) × (fam.Coins × R) |
        fsWinsFull ((fam.determinize p.2.2).adversary (scalarBasis B p.1))
          (fullAlgebraicAccept (scalarBasis B p.1)
            ((fam.determinize p.2.2).vk (scalarBasis B p.1)) ((fam.determinize p.2.2).instanceCommitment (scalarBasis B p.1)))
          (algebraicFullPrefixesPre (fam.determinize p.2.2).init)
          (algebraicFullPrefixes (fam.determinize p.2.2).init) p.2.1.1 ∧
        ¬ (fam.determinize p.2.2).hasCleanOpening (scalarBasis B p.1) p.2.1} ⊆
      {p | p.2.1 ∈ (fam.determinize p.2.2).snarkNonRelationFailure (scalarBasis B p.1)} ∪
      (↑(relSetWithCoins B fam.foldedSnarkRelationFinder) :
        Set ((AugmentedIndex (2 ^ shape.k) → Fp) × (fam.Coins × R)))
        from ?_))
    (le_trans (MeasureTheory.measure_union_le _ _) ?_)
  · intro p hp
    obtain ⟨hacc, hnoclean⟩ := hp
    by_cases hsome : ((fam.determinize p.2.2).instanceAttempt
        (scalarBasis B p.1) p.2.1).output.isSome
    · refine Or.inr ?_
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
      simp only [Finset.mem_coe, relSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and,
        foldedSnarkRelationFinder]
      show ((fam.determinize p.2.2).snarkRelationFinder (scalarBasis B p.1) p.2.1).isSome
      simp only [ComputedAlgebraicFSFamily.snarkRelationFinder, hx]
      cases hrun : x.run with
      | inl o => exact absurd ⟨x, hx, o, hrun⟩ hnoclean
      | inr rel => rfl
    · refine Or.inl ?_
      show p.2.1 ∈ (fam.determinize p.2.2).snarkNonRelationFailure (scalarBasis B p.1)
      unfold ComputedAlgebraicFSFamily.snarkNonRelationFailure
      by_cases hz : p.2.1.1 (algebraicFullPrefixesPre (fam.determinize p.2.2).init
          (((fam.determinize p.2.2).adversary (scalarBasis B p.1)).run p.2.1.1) 10) = 0
      · exact Set.mem_union_right _ ⟨hacc, hz⟩
      · exact Set.mem_union_left _ ⟨⟨hacc, hz⟩, hsome⟩
  · refine add_le_add ?_
      (relationWithCoins_prob_le_of_textbookDL B fam.foldedSnarkRelationFinder hDL)
    apply uniformOfFintype_prod_fiber_bound_right
      (fun coeffs : AugmentedIndex (2 ^ shape.k) → Fp =>
        {cr : fam.Coins × R |
          cr.1 ∈ (fam.determinize cr.2).snarkNonRelationFailure (scalarBasis B coeffs)})
    intro coeffs
    apply uniformOfFintype_prod_fiber_bound
      (fun r : R => {c : fam.Coins |
        c ∈ (fam.determinize r).snarkNonRelationFailure (scalarBasis B coeffs)})
    intro r
    exact (fam.determinize r).snarkNonRelationFailure_measure_le (scalarBasis B coeffs)

end ComputedAlgebraicFSFamilyRand

/-! ## Unbounded-domain programmed-basis endpoint

A common reachable-support split makes the finite junk table private randomness. The endpoint uses
one private-coin-folded DL solver, not a separate assumption for each junk table. -/

/-- A basis-indexed computed adversary over arbitrary transcript lists. -/
structure ComputedAlgebraicFSFamilyUnbounded (shape : Shape) where
  init : List (TranscriptElt Fp VestaG)
  vk : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → VerifyingKey shape Fp VestaG
  instanceCommitment : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → Fin shape.numProofs → ℕ → VestaG
  adversary : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → OracleComp
    (List (TranscriptElt Fp VestaG)) Fp (AlgebraicWfProof basis (vk basis) (instanceCommitment basis))
  Q : ℕ
  queryBound : ∀ basis, (adversary basis).QueryBound Q

/-- Transfer any finite-coin event across a uniform-URS basis identification. -/
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

namespace ComputedAlgebraicFSFamilyUnbounded

variable {shape : Shape}

/-- One finite support containing the reachable support of every basis-indexed adversary. -/
def globalReachSet (family : ComputedAlgebraicFSFamilyUnbounded shape) :
    Finset (List (TranscriptElt Fp VestaG)) := by
  exact Finset.univ.biUnion fun basis : AugmentedIndex (2 ^ shape.k) → VestaG =>
    (family.adversary basis).reachSet

theorem reachSet_subset_globalReachSet (family : ComputedAlgebraicFSFamilyUnbounded shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    (family.adversary basis).reachSet ⊆ family.globalReachSet := by
  intro t ht
  exact Finset.mem_biUnion.mpr ⟨basis, Finset.mem_univ _, ht⟩

/-- Split arbitrary transcripts into the deployed bounded component and a common finite junk
component, then fix the junk table as private randomness. -/
def splitFamilyRand (family : ComputedAlgebraicFSFamilyUnbounded shape) :
    ComputedAlgebraicFSFamilyRand shape
      ({t // t ∈ family.globalReachSet} → Fp) := by
  let L := preIpaLen shape family.init.length 10 + 3 * shape.k
  exact
    { init := family.init
      vk := family.vk
      instanceCommitment := family.instanceCommitment
      adversary := fun basis junk =>
        ((family.adversary basis).splitDomain
          (Subtype.val : BTranscript Fp VestaG L → List (TranscriptElt Fp VestaG))
          (truncateTranscript L) family.globalReachSet
          (family.reachSet_subset_globalReachSet basis)).restrictSum junk
      Q := family.Q
      queryBound := fun basis junk =>
        OracleComp.queryBound_restrictSum
          (OracleComp.queryBound_splitDomain
            (Subtype.val : BTranscript Fp VestaG L → List (TranscriptElt Fp VestaG))
            (truncateTranscript L) family.globalReachSet (family.queryBound basis)
            (family.reachSet_subset_globalReachSet basis)) junk }

/-- Fixing the junk table is semantically exact: the bounded machine runs as the common-support
split machine against the table obtained by adjoining those junk answers. -/
theorem run_splitFamilyRand_adversary (family : ComputedAlgebraicFSFamilyUnbounded shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (junk : {t // t ∈ family.globalReachSet} → Fp)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    (family.splitFamilyRand.adversary basis junk).run O =
      ((family.adversary basis).splitDomain
        (Subtype.val : BTranscript Fp VestaG
            (preIpaLen shape family.init.length 10 + 3 * shape.k) →
          List (TranscriptElt Fp VestaG))
        (truncateTranscript (preIpaLen shape family.init.length 10 + 3 * shape.k))
        family.globalReachSet (family.reachSet_subset_globalReachSet basis)).run
          (Sum.elim O junk) := by
  change (OracleComp.restrictSum junk
    ((family.adversary basis).splitDomain
      (Subtype.val : BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) →
        List (TranscriptElt Fp VestaG))
      (truncateTranscript (preIpaLen shape family.init.length 10 + 3 * shape.k))
      family.globalReachSet (family.reachSet_subset_globalReachSet basis))).run O = _
  exact OracleComp.run_restrictSum junk _ O

/-- Bound arbitrary-domain binding using one DL solver with the junk table folded into its coins. -/
theorem binding_prob_le_of_unbounded_foldedTextbookDL
    (B : VestaG) (family : ComputedAlgebraicFSFamilyUnbounded shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.splitFamilyRand.foldedRelationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) ×
          (family.splitFamilyRand.Coins ×
            ({t // t ∈ family.globalReachSet} → Fp)))).toOuterMeasure
      {p | ComputedAlgebraicFSFamily.bindingWin
        (family.splitFamilyRand.determinize p.2.2) (scalarBasis B p.1) p.2.1}
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  exact ComputedAlgebraicFSFamilyRand.binding_prob_le_of_foldedTextbookDL_rand
    B family.splitFamilyRand hDL

/-- Bound arbitrary-domain clean-opening failure with the junk table folded into the DL coins. -/
theorem snarkFailure_prob_le_of_unbounded_foldedTextbookDL
    (B : VestaG) (family : ComputedAlgebraicFSFamilyUnbounded shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.splitFamilyRand.foldedSnarkRelationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) ×
          (family.splitFamilyRand.Coins ×
            ({t // t ∈ family.globalReachSet} → Fp)))).toOuterMeasure
      {p : (AugmentedIndex (2 ^ shape.k) → Fp) ×
          (family.splitFamilyRand.Coins × ({t // t ∈ family.globalReachSet} → Fp)) |
        fsWinsFull ((family.splitFamilyRand.determinize p.2.2).adversary (scalarBasis B p.1))
          (fullAlgebraicAccept (scalarBasis B p.1)
            ((family.splitFamilyRand.determinize p.2.2).vk (scalarBasis B p.1)) ((family.splitFamilyRand.determinize p.2.2).instanceCommitment (scalarBasis B p.1)))
          (algebraicFullPrefixesPre (family.splitFamilyRand.determinize p.2.2).init)
          (algebraicFullPrefixes (family.splitFamilyRand.determinize p.2.2).init) p.2.1.1 ∧
        ¬ (family.splitFamilyRand.determinize p.2.2).hasCleanOpening (scalarBasis B p.1) p.2.1}
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  exact ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_foldedTextbookDL_rand
    B family.splitFamilyRand hDL

/-- Arbitrary-domain clean-opening failure with the junk table folded into the coins.  The event
is the win event of the common-support *split* machine (`splitFamilyRand.determinize`) over the
finite `BTranscript ⊕ reachSet` domain; `run_splitFamilyRand_adversary` and `run_splitDomain` give
its pointwise faithfulness to the original list-domain adversary, but that composition is not part
of the endpoint statements. -/
def snarkFailureEventUnbounded (family : ComputedAlgebraicFSFamilyUnbounded shape) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) ×
      (family.splitFamilyRand.Coins × ({t // t ∈ family.globalReachSet} → Fp))) :=
  {q | fsWinsFull ((family.splitFamilyRand.determinize q.2.2).adversary q.1)
      (fullAlgebraicAccept q.1 ((family.splitFamilyRand.determinize q.2.2).vk q.1) ((family.splitFamilyRand.determinize q.2.2).instanceCommitment q.1))
      (algebraicFullPrefixesPre (family.splitFamilyRand.determinize q.2.2).init)
      (algebraicFullPrefixes (family.splitFamilyRand.determinize q.2.2).init) q.2.1.1 ∧
    ¬ (family.splitFamilyRand.determinize q.2.2).hasCleanOpening q.1 q.2.1}

/-- Uniform-URS form of the arbitrary-domain clean-opening bound. -/
theorem snarkFailure_prob_le_of_unbounded_uniformURS_textbookDL {Ω : Type*} (setup : PMF Ω)
    (B : VestaG) (family : ComputedAlgebraicFSFamilyUnbounded shape)
    (basisOf : Ω → AugmentedIndex (2 ^ shape.k) → VestaG)
    {bound : ℝ≥0∞} (hURS : OrchardUniformURSIdentification setup shape.k B basisOf)
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.splitFamilyRand.foldedSnarkRelationFinder bound) :
    (independentProductPMF setup (PMF.uniformOfFintype
        (family.splitFamilyRand.Coins ×
          ({t // t ∈ family.globalReachSet} → Fp)))).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' family.snarkFailureEventUnbounded)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  rw [uniformURS_basis_transfer setup B basisOf family.snarkFailureEventUnbounded hURS]
  exact snarkFailure_prob_le_of_unbounded_foldedTextbookDL B family hDL

/-- Generator-RO form of the arbitrary-domain clean-opening bound. -/
theorem snarkFailure_prob_le_of_unbounded_generatorRO_textbookDL
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamilyUnbounded shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.splitFamilyRand.foldedSnarkRelationFinder bound) :
    (independentProductPMF (orchardGeneratorROSetup query) (PMF.uniformOfFintype
        (family.splitFamilyRand.Coins ×
          ({t // t ∈ family.globalReachSet} → Fp)))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkFailureEventUnbounded)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) :=
  snarkFailure_prob_le_of_unbounded_uniformURS_textbookDL (orchardGeneratorROSetup query) B family
    (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery) hDL

/-- Arbitrary-domain binding with the junk table folded into the coins. -/
def bindingEventUnbounded (family : ComputedAlgebraicFSFamilyUnbounded shape) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) ×
      (family.splitFamilyRand.Coins × ({t // t ∈ family.globalReachSet} → Fp))) :=
  {q | ComputedAlgebraicFSFamily.bindingWin (family.splitFamilyRand.determinize q.2.2) q.1 q.2.1}

/-- Uniform-URS form of the arbitrary-domain binding bound. -/
theorem binding_prob_le_of_unbounded_uniformURS_textbookDL {Ω : Type*} (setup : PMF Ω)
    (B : VestaG) (family : ComputedAlgebraicFSFamilyUnbounded shape)
    (basisOf : Ω → AugmentedIndex (2 ^ shape.k) → VestaG)
    {bound : ℝ≥0∞} (hURS : OrchardUniformURSIdentification setup shape.k B basisOf)
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.splitFamilyRand.foldedRelationFinder bound) :
    (independentProductPMF setup (PMF.uniformOfFintype
        (family.splitFamilyRand.Coins ×
          ({t // t ∈ family.globalReachSet} → Fp)))).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' family.bindingEventUnbounded)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  rw [uniformURS_basis_transfer setup B basisOf family.bindingEventUnbounded hURS]
  exact binding_prob_le_of_unbounded_foldedTextbookDL B family hDL

/-- Generator-RO form of the arbitrary-domain binding bound. -/
theorem binding_prob_le_of_unbounded_generatorRO_textbookDL
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamilyUnbounded shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.splitFamilyRand.foldedRelationFinder bound) :
    (independentProductPMF (orchardGeneratorROSetup query) (PMF.uniformOfFintype
        (family.splitFamilyRand.Coins ×
          ({t // t ∈ family.globalReachSet} → Fp)))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.bindingEventUnbounded)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) :=
  binding_prob_le_of_unbounded_uniformURS_textbookDL (orchardGeneratorROSetup query) B family
    (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery) hDL

end ComputedAlgebraicFSFamilyUnbounded

/-- Arbitrary-domain adversary with genuine independent private coins `R`, on top of the
transcript-list oracle domain. -/
structure ComputedAlgebraicFSFamilyUnboundedRand (shape : Shape) (R : Type*) where
  init : List (TranscriptElt Fp VestaG)
  vk : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → VerifyingKey shape Fp VestaG
  instanceCommitment : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → Fin shape.numProofs → ℕ → VestaG
  adversary : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → R → OracleComp
    (List (TranscriptElt Fp VestaG)) Fp (AlgebraicWfProof basis (vk basis) (instanceCommitment basis))
  Q : ℕ
  queryBound : ∀ basis r, (adversary basis r).QueryBound Q

namespace ComputedAlgebraicFSFamilyUnboundedRand

variable {shape : Shape} {R : Type*}

/-- Fix the private coin. -/
def determinize (family : ComputedAlgebraicFSFamilyUnboundedRand shape R) (r : R) :
    ComputedAlgebraicFSFamilyUnbounded shape :=
  { init := family.init
    vk := family.vk
    instanceCommitment := family.instanceCommitment
    adversary := fun basis => family.adversary basis r
    Q := family.Q
    queryBound := fun basis => family.queryBound basis r }

/-- One finite support covering the reachable support of every basis *and every private coin*. -/
def globalReachSet [Fintype R]
    (family : ComputedAlgebraicFSFamilyUnboundedRand shape R) :
    Finset (List (TranscriptElt Fp VestaG)) := by
  exact Finset.univ.biUnion fun basis : AugmentedIndex (2 ^ shape.k) → VestaG =>
    Finset.univ.biUnion fun r : R => (family.adversary basis r).reachSet

theorem reachSet_subset_globalReachSet [Fintype R]
    (family : ComputedAlgebraicFSFamilyUnboundedRand shape R)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (r : R) :
    (family.adversary basis r).reachSet ⊆ family.globalReachSet := by
  intro t ht
  exact Finset.mem_biUnion.mpr ⟨basis, Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, ht⟩⟩

/-- Split against the shared support, pairing the genuine private coin with the junk table: a
bounded randomized family at coin type `R × junk`. -/
def splitFamilyRand [Fintype R]
    (family : ComputedAlgebraicFSFamilyUnboundedRand shape R) :
    ComputedAlgebraicFSFamilyRand shape
      (R × ({t // t ∈ family.globalReachSet} → Fp)) := by
  let L := preIpaLen shape family.init.length 10 + 3 * shape.k
  exact
    { init := family.init
      vk := family.vk
      instanceCommitment := family.instanceCommitment
      adversary := fun basis rc =>
        ((family.adversary basis rc.1).splitDomain
          (Subtype.val : BTranscript Fp VestaG L → List (TranscriptElt Fp VestaG))
          (truncateTranscript L) family.globalReachSet
          (family.reachSet_subset_globalReachSet basis rc.1)).restrictSum rc.2
      Q := family.Q
      queryBound := fun basis rc =>
        OracleComp.queryBound_restrictSum
          (OracleComp.queryBound_splitDomain
            (Subtype.val : BTranscript Fp VestaG L → List (TranscriptElt Fp VestaG))
            (truncateTranscript L) family.globalReachSet (family.queryBound basis rc.1)
            (family.reachSet_subset_globalReachSet basis rc.1)) rc.2 }

/-- Fixing the coin pair is semantically exact: the bounded machine runs as the coin-fixed
common-support split machine against the table obtained by adjoining the junk answers. -/
theorem run_splitFamilyRand_adversary [Fintype R]
    (family : ComputedAlgebraicFSFamilyUnboundedRand shape R)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (r : R)
    (junk : {t // t ∈ family.globalReachSet} → Fp)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    (family.splitFamilyRand.adversary basis (r, junk)).run O =
      ((family.adversary basis r).splitDomain
        (Subtype.val : BTranscript Fp VestaG
            (preIpaLen shape family.init.length 10 + 3 * shape.k) →
          List (TranscriptElt Fp VestaG))
        (truncateTranscript (preIpaLen shape family.init.length 10 + 3 * shape.k))
        family.globalReachSet (family.reachSet_subset_globalReachSet basis r)).run
          (Sum.elim O junk) := by
  change (OracleComp.restrictSum junk
    ((family.adversary basis r).splitDomain
      (Subtype.val : BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) →
        List (TranscriptElt Fp VestaG))
      (truncateTranscript (preIpaLen shape family.init.length 10 + 3 * shape.k))
      family.globalReachSet (family.reachSet_subset_globalReachSet basis r))).run O = _
  exact OracleComp.run_restrictSum junk _ O

/-- Bound randomized arbitrary-domain binding using one DL solver with the private coin and the
junk table folded into its coins. -/
theorem binding_prob_le_of_unboundedRand_foldedTextbookDL [Fintype R] [Nonempty R]
    (B : VestaG) (family : ComputedAlgebraicFSFamilyUnboundedRand shape R) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.splitFamilyRand.foldedRelationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) ×
          (family.splitFamilyRand.Coins ×
            (R × ({t // t ∈ family.globalReachSet} → Fp))))).toOuterMeasure
      {p | ComputedAlgebraicFSFamily.bindingWin
        (family.splitFamilyRand.determinize p.2.2) (scalarBasis B p.1) p.2.1}
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  exact ComputedAlgebraicFSFamilyRand.binding_prob_le_of_foldedTextbookDL_rand
    B family.splitFamilyRand hDL

/-- Bound randomized arbitrary-domain clean-opening failure with the private coin and the junk
table folded into the DL coins. -/
theorem snarkFailure_prob_le_of_unboundedRand_foldedTextbookDL [Fintype R] [Nonempty R]
    (B : VestaG) (family : ComputedAlgebraicFSFamilyUnboundedRand shape R) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.splitFamilyRand.foldedSnarkRelationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) ×
          (family.splitFamilyRand.Coins ×
            (R × ({t // t ∈ family.globalReachSet} → Fp))))).toOuterMeasure
      {p : (AugmentedIndex (2 ^ shape.k) → Fp) ×
          (family.splitFamilyRand.Coins ×
            (R × ({t // t ∈ family.globalReachSet} → Fp))) |
        fsWinsFull ((family.splitFamilyRand.determinize p.2.2).adversary (scalarBasis B p.1))
          (fullAlgebraicAccept (scalarBasis B p.1)
            ((family.splitFamilyRand.determinize p.2.2).vk (scalarBasis B p.1)) ((family.splitFamilyRand.determinize p.2.2).instanceCommitment (scalarBasis B p.1)))
          (algebraicFullPrefixesPre (family.splitFamilyRand.determinize p.2.2).init)
          (algebraicFullPrefixes (family.splitFamilyRand.determinize p.2.2).init) p.2.1.1 ∧
        ¬ (family.splitFamilyRand.determinize p.2.2).hasCleanOpening (scalarBasis B p.1) p.2.1}
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  exact ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_foldedTextbookDL_rand
    B family.splitFamilyRand hDL

/-- Randomized arbitrary-domain clean-opening failure, private coin and junk table in the coins.
As in the deterministic case, the event is the win event of the common-support split machine;
`run_splitFamilyRand_adversary` gives its pointwise faithfulness. -/
def snarkFailureEventUnboundedRand [Fintype R]
    (family : ComputedAlgebraicFSFamilyUnboundedRand shape R) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) ×
      (family.splitFamilyRand.Coins ×
        (R × ({t // t ∈ family.globalReachSet} → Fp)))) :=
  {q | fsWinsFull ((family.splitFamilyRand.determinize q.2.2).adversary q.1)
      (fullAlgebraicAccept q.1 ((family.splitFamilyRand.determinize q.2.2).vk q.1) ((family.splitFamilyRand.determinize q.2.2).instanceCommitment q.1))
      (algebraicFullPrefixesPre (family.splitFamilyRand.determinize q.2.2).init)
      (algebraicFullPrefixes (family.splitFamilyRand.determinize q.2.2).init) q.2.1.1 ∧
    ¬ (family.splitFamilyRand.determinize q.2.2).hasCleanOpening q.1 q.2.1}

/-- Uniform-URS form of the randomized arbitrary-domain clean-opening bound. -/
theorem snarkFailure_prob_le_of_unboundedRand_uniformURS_textbookDL [Fintype R] [Nonempty R]
    {Ω : Type*} (setup : PMF Ω)
    (B : VestaG) (family : ComputedAlgebraicFSFamilyUnboundedRand shape R)
    (basisOf : Ω → AugmentedIndex (2 ^ shape.k) → VestaG)
    {bound : ℝ≥0∞} (hURS : OrchardUniformURSIdentification setup shape.k B basisOf)
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.splitFamilyRand.foldedSnarkRelationFinder bound) :
    (independentProductPMF setup (PMF.uniformOfFintype
        (family.splitFamilyRand.Coins ×
          (R × ({t // t ∈ family.globalReachSet} → Fp))))).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' family.snarkFailureEventUnboundedRand)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  rw [uniformURS_basis_transfer setup B basisOf family.snarkFailureEventUnboundedRand hURS]
  exact snarkFailure_prob_le_of_unboundedRand_foldedTextbookDL B family hDL

/-- Generator-RO form of the randomized arbitrary-domain clean-opening bound. -/
theorem snarkFailure_prob_le_of_unboundedRand_generatorRO_textbookDL [Fintype R] [Nonempty R]
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamilyUnboundedRand shape R) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.splitFamilyRand.foldedSnarkRelationFinder bound) :
    (independentProductPMF (orchardGeneratorROSetup query) (PMF.uniformOfFintype
        (family.splitFamilyRand.Coins ×
          (R × ({t // t ∈ family.globalReachSet} → Fp))))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkFailureEventUnboundedRand)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) :=
  snarkFailure_prob_le_of_unboundedRand_uniformURS_textbookDL (orchardGeneratorROSetup query)
    B family (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery) hDL

/-- Randomized arbitrary-domain binding, private coin and junk table in the coins. -/
def bindingEventUnboundedRand [Fintype R]
    (family : ComputedAlgebraicFSFamilyUnboundedRand shape R) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) ×
      (family.splitFamilyRand.Coins ×
        (R × ({t // t ∈ family.globalReachSet} → Fp)))) :=
  {q | ComputedAlgebraicFSFamily.bindingWin (family.splitFamilyRand.determinize q.2.2) q.1 q.2.1}

/-- Uniform-URS form of the randomized arbitrary-domain binding bound. -/
theorem binding_prob_le_of_unboundedRand_uniformURS_textbookDL [Fintype R] [Nonempty R]
    {Ω : Type*} (setup : PMF Ω)
    (B : VestaG) (family : ComputedAlgebraicFSFamilyUnboundedRand shape R)
    (basisOf : Ω → AugmentedIndex (2 ^ shape.k) → VestaG)
    {bound : ℝ≥0∞} (hURS : OrchardUniformURSIdentification setup shape.k B basisOf)
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.splitFamilyRand.foldedRelationFinder bound) :
    (independentProductPMF setup (PMF.uniformOfFintype
        (family.splitFamilyRand.Coins ×
          (R × ({t // t ∈ family.globalReachSet} → Fp))))).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' family.bindingEventUnboundedRand)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  rw [uniformURS_basis_transfer setup B basisOf family.bindingEventUnboundedRand hURS]
  exact binding_prob_le_of_unboundedRand_foldedTextbookDL B family hDL

/-- Generator-RO form of the randomized arbitrary-domain binding bound. -/
theorem binding_prob_le_of_unboundedRand_generatorRO_textbookDL [Fintype R] [Nonempty R]
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamilyUnboundedRand shape R) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.splitFamilyRand.foldedRelationFinder bound) :
    (independentProductPMF (orchardGeneratorROSetup query) (PMF.uniformOfFintype
        (family.splitFamilyRand.Coins ×
          (R × ({t // t ∈ family.globalReachSet} → Fp))))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.bindingEventUnboundedRand)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) :=
  binding_prob_le_of_unboundedRand_uniformURS_textbookDL (orchardGeneratorROSetup query)
    B family (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery) hDL

end ComputedAlgebraicFSFamilyUnboundedRand

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
def AlgebraicPoint.gPart (P : AlgebraicPoint (F := Fp) basis) : Fin (2 ^ shape.k) → Fp :=
  fun i => P.coeffs (AugmentedIndex.gen i)

/-- An augmented-basis point is its generator commitment plus its declared `U` and `W`
components. -/
theorem AlgebraicPoint.point_eq_components (P : AlgebraicPoint (F := Fp) basis) :
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
