import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.RedDSA.Basic
import Zcash.Snark.Soundness.AGM.Adapter

/-!
# RedDSA extractability: a verifying binding signature computes a discrete-log relation

The binding signature is a signature of knowledge of `bsk = Σ rcv`, the discrete log of the
binding validating key `bvk` with respect to the value-commitment randomness base `ℛ`
(spec §5.4.7.2). The balance argument needs this knowledge property, and needs it in the
proof-of-knowledge direction, not the unforgeability direction: `bvk` is the adversary's own
key, computed from its bundle's value commitments, so what we extract from is the adversary's
own verifying signature.

This module proves the deterministic core of that extraction. In the algebraic group model
every group element the adversary presents carries a representation over the public bases it
has received — here an arbitrary finite family, with the ℛ slot distinguished (`r_idx`).
`QueryRep` is the representation data for one signature: the coefficient vectors of the
commitment `R` and of the key `bvk`. Substituting them into the Schnorr verification equation
`[S] ℛ = R + [c] bvk` at challenge `c` assembles the coefficients
`commitment + c · key − S · e_ℛ` (`QueryRep.assembled`), whose evaluation against the basis is
zero. Whenever some assembled coordinate is nonzero, that is an `AlgebraicRelationWitness`
(`bindingSig_relation_of_nontrivial`). Extraction failure forces a nonzero slope coefficient
away from the ℛ slot: a key represented on the ℛ slot alone is `key r_idx • ℛ`, and the
extractor that reads `key r_idx` succeeds there
(`QueryRep.representationEval_key_of_pivot_eq_none`). The first such slot is the pivot
(`QueryRep.pivot`), and at most one challenge — the root of the pivot slot's linear
equation — makes every assembled coordinate vanish (`QueryRep.badChallenge`,
`QueryRep.assembled_ne_zero_of_ne_badChallenge`).

That exceptional challenge is the only probabilistic ingredient. In the random-oracle
heuristic `c = H(R, bvk, sighash)` is drawn after the representations are fixed, so it hits
the bad challenge with probability at most `1/|𝔽_{r_ℙ}|` per query. A guessing argument over
the query budget accounts for it, and the relation feeds the existing
`relation_prob_le_of_textbookDL` reduction to discrete log. Those two steps are the intended
completion of the κ-discharge; this file is the deterministic relation extraction they
consume.

The straight-line extraction technique is the one Fuchsbauer, Plouviez, and Seurin use for
Schnorr (eprint 2019/877, section 3, Theorem 1). The SURK-CMA unforgeability game and its
reduction (#121) remain unmodelled, but assuming that the reduction can follow the same
approach as FPS Theorem 1, it likely will be able to use the same extraction with a signing
oracle added. The relation feeds a reduction that models the public bases as independent
random group elements; the reference-string heuristic that carries this to the deployed fixed
hash-to-curve bases, and its lifetime caveat, is described in the book (Security
Definitions).

`Extractor` and `ExtractionFailure` state the obligation as data: a candidate extractor is a
total function, and where it fails is an exhibited event, so κ bounds an exhibited event rather
than a total extraction hypothesis (classically satisfiable in a cyclic group — see the module
doc of `Zcash.Security.Ledger.Value`). Nothing fixes an honest key: the extractor must succeed
at any adversary-chosen vk, and an adversary who produces a verifying signature without knowing
the key lands exactly in the extraction-failure event. (At this instantiation the arbitrary-key
and honest-key settings are close: sk + α at uniform α is distributed as a fresh key, so a
reduction can randomize the key, run a key-recovery adversary, and undo the randomization —
`randomizePrivate_add_neg`. That rests on the connection between public and private keys in a
prime-order group; it is not definitionally true for signature schemes in general.)
-/

namespace Zcash.Security.RedDSA

open Zcash.Snark

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-! ### Extraction failure, as data -/

/-- A candidate knowledge extractor: from a verifying (vk, m, σ) it should return
dlog_{𝒫_𝔾} vk. Total as a function; where it fails is exactly the event the
knowledge error bounds. -/
abbrev Extractor (F G MSG : Type*) := G → MSG → Sig F G → F

/-- An extraction failure, as data: a verifying signature on which the extractor does
not return the discrete log of vk. The knowledge obligation on BindingSig — "a
signature must prove knowledge of the discrete logarithm of the validating key with
respect to the base ℛ" (spec §5.4.7.2) — is the named bound κ on the probability
that an adversary exhibits this event; the known discharge routes are in the module
doc of `Zcash.Security.RedDSA.Basic`. -/
structure ExtractionFailure {MSG : Type*} (sch : Scheme F M MSG) (E : Extractor F M MSG) where
  vk : M
  m : MSG
  σ : Sig F M
  verifies : sch.Verify vk m σ
  ne : vk ≠ E vk m σ • sch.base

/-! ### Signature representations over the public basis -/

/-- The representation of one signature's group elements over the `m` public bases the
adversary has received: coefficient vectors for the commitment `R` and the binding validating
key `bvk`. Slot `r_idx` holds the value-commitment randomness base ℛ (the Schnorr base of the
binding signature); which public points fill the other slots is the instantiation's choice.
An algebraic adversary fixes these vectors when it presents the elements — at its challenge
query, before the oracle's answer is drawn (Fuchsbauer–Plouviez–Seurin, eprint 2019/877,
section 2) — which is what makes the bad challenge below a guessable target. -/
structure QueryRep (F : Type*) (m : ℕ) where
  commitment : Fin m → F
  key : Fin m → F

instance {F : Type*} [Zero F] {m : ℕ} : Inhabited (QueryRep F m) := ⟨⟨0, 0⟩⟩

namespace QueryRep

variable {m : ℕ}

/-- The coefficients assembled from the Schnorr verification equation at challenge `c` and
response `S`: `commitment + c · key`, minus `S` at the ℛ slot. -/
def assembled (t : QueryRep F m) (r_idx : Fin m) (c S : F) : Fin m → F :=
  fun i => t.commitment i + c * t.key i - if i = r_idx then S else 0

variable [DecidableEq F]

/-- The pivot: the first non-ℛ slot at which the key's coefficient — the challenge's slope in
the assembled coefficients — is nonzero. Extraction failure forces the pivot to exist: with no
pivot the key is on the ℛ line (`representationEval_key_of_pivot_eq_none`), where the
extractor that reads `key r_idx` succeeds. -/
def pivot (t : QueryRep F m) (r_idx : Fin m) : Option (Fin m) :=
  (List.finRange m).find? fun i => decide (i ≠ r_idx ∧ t.key i ≠ 0)

/-- With no pivot, the represented key element is `key r_idx • ℛ`. -/
theorem representationEval_key_of_pivot_eq_none (t : QueryRep F m) (r_idx : Fin m)
    (basis : Fin m → M) (h : t.pivot r_idx = none) :
    representationEval basis t.key = t.key r_idx • basis r_idx := by
  rw [pivot] at h
  refine Fintype.sum_eq_single r_idx fun i hi => ?_
  have hzero := List.find?_eq_none.mp h i (List.mem_finRange i)
  simp only [decide_eq_true_eq, not_and, not_not] at hzero
  rw [hzero hi, zero_smul]

/-- The bad challenge: the single root of the pivot slot's assembled coefficient, and a junk
value when there is no pivot. -/
def badChallenge (t : QueryRep F m) (r_idx : Fin m) : F :=
  match t.pivot r_idx with
  | some j => -(t.commitment j / t.key j)
  | none => 0

/-- **At most one bad challenge.** With a pivot present, every challenge other than
`badChallenge` makes the assembled coefficients nonzero (at the pivot slot). -/
theorem assembled_ne_zero_of_ne_badChallenge {t : QueryRep F m} {r_idx j : Fin m} {c S : F}
    (hj : t.pivot r_idx = some j) (hc : c ≠ t.badChallenge r_idx) :
    t.assembled r_idx c S ≠ 0 := by
  have hjprop : j ≠ r_idx ∧ t.key j ≠ 0 := by
    have := List.find?_some (by rw [pivot] at hj; exact hj)
    simpa using this
  intro h0
  have hcoord := congrFun h0 j
  simp only [assembled, if_neg hjprop.1, sub_zero, Pi.zero_apply] at hcoord
  apply hc
  rw [badChallenge, hj]
  show c = -(t.commitment j / t.key j)
  rw [← neg_div]
  exact eq_div_of_mul_eq hjprop.2 (by linear_combination hcoord)

end QueryRep

/-- **A verifying binding signature computes a discrete-log relation.** Substituting the
representations of `R` and `bvk` into the Schnorr verification equation `[S] ℛ = R + [c] bvk`
makes the assembled coefficients evaluate to zero against the basis, so whenever they are
nonzero somewhere they are an `AlgebraicRelationWitness`.
`QueryRep.assembled_ne_zero_of_ne_badChallenge` provides the nonzeroness away from the one
bad challenge. -/
def bindingSig_relation_of_nontrivial {m : ℕ} (basis : Fin m → M) (r_idx : Fin m)
    (t : QueryRep F m) (c S : F)
    (hverify : S • basis r_idx
      = representationEval basis t.commitment + c • representationEval basis t.key)
    (hnt : t.assembled r_idx c S ≠ 0) :
    AlgebraicRelationWitness (F := F) basis where
  coeffs := t.assembled r_idx c S
  nontrivial := hnt
  relation := by
    have hsplit : representationEval basis (t.assembled r_idx c S)
        = representationEval basis t.commitment + c • representationEval basis t.key
          - S • basis r_idx := by
      simp only [representationEval, QueryRep.assembled, sub_smul, add_smul, ite_smul,
        zero_smul, mul_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ r_idx, Finset.mem_univ, if_true, Finset.smul_sum]
    rw [hsplit, ← hverify, sub_self]

end Zcash.Security.RedDSA
