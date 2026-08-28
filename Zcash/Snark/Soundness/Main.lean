import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Verifier.Deployed
import Zcash.Snark.Verifier.KeyDigest
import Zcash.Snark.Verifier.ProofBytes
import Zcash.Snark.Soundness.Deployed.Verification

/-!
# Conditional soundness and deployed acceptance

Soundness starts from `DeployedAccepts`: `assemble?` succeeds and the resulting MSM evaluates to
zero. The adaptive and straight-line AGM routes consume this predicate directly.

## The deployed route

`deployedAccepts_verifierEq` exposes the equivalent flattened IPA equation used by the current
straight-line AGM analysis. Extraction and Action semantics live in `Soundness.AGM` and
`Circuits.Integration`; this module intentionally exports no forked-transcript compatibility lane.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

variable {G : Type*} [AddCommGroup G] [Module Fp G]

-- Semantic reach of the chain built on this predicate: `TopLevelCircuitCorrectness`'s component
-- conditions are discharged for the deployed Action circuit, so the adaptive-statement stack ends
-- at `ActionTerminal.ActionBundleWitness` — the circuit's private witnesses with their `ActionSpec`
-- satisfaction proofs at the adversary's public inputs — rather than at gate satisfaction. The
-- remaining output-side boundary is composing `ActionSpec`, including its `HashGuarded` Sinsemilla
-- escape branches, with the abstract Orchard ledger relation. On the input side, the deployed Action
-- key is derived and certified against the capture by `Keygen/Certificate.lean`; the exact captured
-- proof bytes are parsed and composed with acceptance below. Universal refinement of the Rust reader
-- by `readProof?` remains external.
/-- **Deployed acceptance.** `assemble?` succeeds on the typed proof string and the assembled MSM
evaluates to zero over the URS — the hypothesis every soundness endpoint consumes.

This is the reusable typed core. `DeployedAcceptsBytes` below composes exact proof parsing, the
derived verifying-key digest, and the deployed BLAKE2b Fiat–Shamir transcript into it. Acceptance
prices one proof bundle: halo2's optional `BatchVerifier` aggregation layer is outside the
formalized verifier. -/
def DeployedAccepts [DecidableEq G] [Inhabited G] (shape : Shape) (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop :=
  match assemble? vk instanceCommitment ps ch with
  | some m => (hk ▸ m : Msm urs.k Fp G).eval urs = 0
  | none => False

/-- Typed acceptance depends on public-instance commitments only at columns actually named by the
verifying key. -/
theorem deployedAccepts_congr_instanceCommitment [DecidableEq G] [Inhabited G]
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k}
    {vk : VerifyingKey shape Fp G}
    {instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    (hcommit : ∀ p column rotation, (column, rotation) ∈ vk.instanceQueryLayout →
      instanceCommitment p column = instanceCommitment' p column)
    (h : DeployedAccepts shape urs hk vk instanceCommitment ps ch) :
    DeployedAccepts shape urs hk vk instanceCommitment' ps ch := by
  unfold DeployedAccepts at h ⊢
  rw [← assemble?_congr_instanceCommitment vk instanceCommitment instanceCommitment'
    ps ch hcommit]
  exact h

/-- **Byte-level deployed acceptance.** The pinned description describes the designated canonical
key and the key actually checked agrees with it on every verifier-reachable field
(`Describes`); no absorbed instance commitment is the identity, which halo2's
`common_point` refuses where the total `pointBytes` would encode it as `(0, 0)`; the whole proof
byte string parses canonically and with no unread suffix; and the existing typed `DeployedAccepts`
predicate holds at challenges derived by the deployed BLAKE2b transcript, opened with
`keyDigest pinnedVkDescription`.

The separate `canonicalVk` argument is necessary because Halo2's pinned description omits derived
runtime fields. `Describes` checks its represented fields against `canonicalVk` and binds every
verifier-active field of `vk`, including `blindingFactors`, `delta`, `chunkLen`, the permutation
partition, and common-evaluation indices, to that key. It remains a relation: the Action caller
supplies the circuit-derived key and separately pins the exact exporter-emitted description.

Nor does `Describes` derive every reader count. The caller's `Shape` supplies
`numQuotientPieces` and `numPointSets`; the Action instantiation obtains the former from circuit
derivation and the latter from proof parameters. `numPermutationSets` is checked against the key's
chunk count while regular chunking is a separate circuit/key agreement. Exact parsing therefore
includes those deployment-shape identifications rather than proving them from the description.

The empty suffix is intentional. Halo2's reader itself ignores unread bytes; the production
transaction/bundle boundary modeled here separately checks the canonical total length
`2720 + 2272 · nActionsOrchard` — ZIP 225's format value, a consensus rule from NU6.2 onward
(ZIP 257), which `zcash_primitives` enforces for NU6.2-and-later bundles and leaves unenforced
for earlier epochs. Thus this predicate models the exact canonical-byte path of the fixed
circuit's epoch, and a Rust acceptance relation must include that outer check before it can refine
this predicate.

Identifying Rust's reader with `readProof?` for every input remains a refinement boundary; the
exact honest and random capture bytes exercise that boundary concretely. -/
def DeployedAcceptsBytes [Inhabited VestaG] (shape : Shape) (urs : URS VestaG)
    (hk : shape.k = urs.k)
    (canonicalVk vk : VerifyingKey shape Fp VestaG) (pinnedVkDescription : String)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (proofBytes : List UInt8) : Prop :=
  Describes pinnedVkDescription canonicalVk vk ∧
  (∀ p (column : Fin shape.numInstanceColumns), instanceCommitment p column ≠ 0) ∧
  ∃ ps,
    (readProof? shape).run proofBytes = some (ps, []) ∧
    DeployedAccepts shape urs hk vk instanceCommitment ps
      (deriveChallengesForStatement halo2Transcript (keyDigest pinnedVkDescription)
        instanceCommitment ps)

/-- Byte-level acceptance exposes the unique parsed proof and its canonical serialization before
entering typed `DeployedAccepts`, alongside the key identification and the identity exclusion. -/
theorem deployedAcceptsBytes_canonical [Inhabited VestaG] {shape : Shape} {urs : URS VestaG}
    {hk : shape.k = urs.k} {canonicalVk vk : VerifyingKey shape Fp VestaG}
    {pinnedVkDescription : String}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} {proofBytes : List UInt8}
    (h : DeployedAcceptsBytes shape urs hk canonicalVk vk pinnedVkDescription
      instanceCommitment proofBytes) :
    Describes pinnedVkDescription canonicalVk vk ∧
    (∀ p (column : Fin shape.numInstanceColumns), instanceCommitment p column ≠ 0) ∧
    ∃ ps,
      (readProof? shape).run proofBytes = some (ps, []) ∧
      serializeProof ps = proofBytes ∧
      DeployedAccepts shape urs hk vk instanceCommitment ps
        (deriveChallengesForStatement halo2Transcript (keyDigest pinnedVkDescription)
          instanceCommitment ps) := by
  rcases h with ⟨hdesc, hne, ps, hread, haccepts⟩
  exact ⟨hdesc, hne, ps, hread, serializeProof_eq_of_readProof?_eq_some hread, haccepts⟩

/-- Byte acceptance is extensional over configured commitments for Fiat–Shamir and over the
verifying key's registered instance-query layout for assembly.  The two hypotheses are separate
because the internal commitment family is historically represented as a total function on natural
column indices. -/
theorem deployedAcceptsBytes_congr_instanceCommitment [Inhabited VestaG]
    {shape : Shape} {urs : URS VestaG} {hk : shape.k = urs.k}
    {canonicalVk vk : VerifyingKey shape Fp VestaG} {pinnedVkDescription : String}
    {instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → VestaG}
    {proofBytes : List UInt8}
    (hconfigured : ∀ p (column : Fin shape.numInstanceColumns),
      instanceCommitment p column = instanceCommitment' p column)
    (hlayout : ∀ p column rotation, (column, rotation) ∈ vk.instanceQueryLayout →
      instanceCommitment p column = instanceCommitment' p column)
    (h : DeployedAcceptsBytes shape urs hk canonicalVk vk pinnedVkDescription
      instanceCommitment proofBytes) :
    DeployedAcceptsBytes shape urs hk canonicalVk vk pinnedVkDescription
      instanceCommitment' proofBytes := by
  rcases h with ⟨hdesc, hne, ps, hread, haccepts⟩
  refine ⟨hdesc, ?_, ps, hread, ?_⟩
  · intro p column
    rw [← hconfigured p column]
    exact hne p column
  · have hch := deriveChallengesForStatement_congr halo2Transcript
      (keyDigest pinnedVkDescription) instanceCommitment instanceCommitment' ps hconfigured
    rw [← hch]
    exact deployedAccepts_congr_instanceCommitment hlayout haccepts

/-- **Raw-instance and proof-byte deployed acceptance.** Public columns must first pass Halo2's
exact column-count and usable-row checks. Their commitments are then derived from that validated
value and supplied to `DeployedAcceptsBytes`; callers cannot inject a detached commitment family.

`commitColumn` is the deployment's Lagrange-basis commitment operation. For Action it is
instantiated by the circuit-derived `commitLagrange`; the caller's exact ten-row serialization is
the separate wrapper obligation because Halo2 intentionally accepts shorter trailing-zero aliases. -/
def DeployedAcceptsRawBytes [Inhabited VestaG] (shape : Shape) (urs : URS VestaG)
    (hk : shape.k = urs.k)
    (canonicalVk vk : VerifyingKey shape Fp VestaG) (pinnedVkDescription : String)
    (instances : RawInstances shape Fp) (commitColumn : List Fp → VestaG)
    (proofBytes : List UInt8) : Prop :=
  ∃ valid : ValidatedInstances vk,
    validateInstances? vk instances = some valid ∧
    DeployedAcceptsBytes shape urs hk canonicalVk vk pinnedVkDescription
      (valid.commitments commitColumn) proofBytes

/-- Raw acceptance exposes the validated columns and enters the existing byte-level predicate with
exactly their derived commitments. -/
theorem deployedAcceptsRawBytes_to_bytes [Inhabited VestaG]
    {shape : Shape} {urs : URS VestaG} {hk : shape.k = urs.k}
    {canonicalVk vk : VerifyingKey shape Fp VestaG} {pinnedVkDescription : String}
    {instances : RawInstances shape Fp} {commitColumn : List Fp → VestaG}
    {proofBytes : List UInt8}
    (h : DeployedAcceptsRawBytes shape urs hk canonicalVk vk pinnedVkDescription
      instances commitColumn proofBytes) :
    ∃ valid : ValidatedInstances vk,
      validateInstances? vk instances = some valid ∧
      DeployedAcceptsBytes shape urs hk canonicalVk vk pinnedVkDescription
        (valid.commitments commitColumn) proofBytes :=
  h

/-- Successful raw acceptance exposes the validated public columns, the unique proof parsed from
the complete byte string, its canonical serialization, and the typed acceptance judgment reached
with commitments derived from those columns.  This is the complete Lean raw-to-typed bridge; it
does not identify an independently implemented Rust reader with `readProof?`. -/
theorem deployedAcceptsRawBytes_canonical [Inhabited VestaG]
    {shape : Shape} {urs : URS VestaG} {hk : shape.k = urs.k}
    {canonicalVk vk : VerifyingKey shape Fp VestaG} {pinnedVkDescription : String}
    {instances : RawInstances shape Fp} {commitColumn : List Fp → VestaG}
    {proofBytes : List UInt8}
    (h : DeployedAcceptsRawBytes shape urs hk canonicalVk vk pinnedVkDescription
      instances commitColumn proofBytes) :
    ∃ valid : ValidatedInstances vk,
      validateInstances? vk instances = some valid ∧
      Describes pinnedVkDescription canonicalVk vk ∧
      (∀ p (column : Fin shape.numInstanceColumns),
        valid.commitments commitColumn p column ≠ 0) ∧
      ∃ ps,
        (readProof? shape).run proofBytes = some (ps, []) ∧
        serializeProof ps = proofBytes ∧
        DeployedAccepts shape urs hk vk (valid.commitments commitColumn) ps
          (deriveChallengesForStatement halo2Transcript (keyDigest pinnedVkDescription)
            (valid.commitments commitColumn) ps) := by
  rcases h with ⟨valid, hvalid, hbytes⟩
  rcases deployedAcceptsBytes_canonical hbytes with
    ⟨hdesc, hne, ps, hread, hserialize, haccepts⟩
  exact ⟨valid, hvalid, hdesc, hne, ps, hread, hserialize, haccepts⟩

/-- A wrong number of instance columns is rejected before byte-level acceptance. -/
theorem deployedAcceptsRawBytes_not_of_wrong_column_count [Inhabited VestaG]
    {shape : Shape} {urs : URS VestaG} {hk : shape.k = urs.k}
    {canonicalVk vk : VerifyingKey shape Fp VestaG} {pinnedVkDescription : String}
    {instances : RawInstances shape Fp} {commitColumn : List Fp → VestaG}
    {proofBytes : List UInt8} (hcount : ¬ InstancesHaveExpectedColumnCount instances) :
    ¬ DeployedAcceptsRawBytes shape urs hk canonicalVk vk pinnedVkDescription
      instances commitColumn proofBytes := by
  rintro ⟨valid, hvalid, _⟩
  rw [validateInstances?_eq_none_of_wrong_column_count vk instances hcount] at hvalid
  contradiction

/-- An oversized instance column is rejected before byte-level acceptance. -/
theorem deployedAcceptsRawBytes_not_of_oversized_column [Inhabited VestaG]
    {shape : Shape} {urs : URS VestaG} {hk : shape.k = urs.k}
    {canonicalVk vk : VerifyingKey shape Fp VestaG} {pinnedVkDescription : String}
    {instances : RawInstances shape Fp} {commitColumn : List Fp → VestaG}
    {proofBytes : List UInt8} (hcount : InstancesHaveExpectedColumnCount instances)
    (hfit : ¬ InstanceColumnsFit vk instances) :
    ¬ DeployedAcceptsRawBytes shape urs hk canonicalVk vk pinnedVkDescription
      instances commitColumn proofBytes := by
  rintro ⟨valid, hvalid, _⟩
  rw [validateInstances?_eq_none_of_oversized_column vk instances hcount hfit] at hvalid
  contradiction

/-- Transport MSM evaluation across the equality `shape.k = urs.k`. -/
theorem eval_cast {shape : Shape} {urs : URS G} (hk : shape.k = urs.k) (m : Msm shape.k Fp G) :
    (hk ▸ m : Msm urs.k Fp G).eval urs = m.eval ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
  -- With `urs` free, destructuring + `subst hk` collapses the cast to `rfl`. Isolating the
  -- transport here keeps `deployedAccepts_verifierEq` from destructuring the URS in place,
  -- which would tangle the accept hypothesis's own `hk`-cast.
  obtain ⟨k, g, w, u⟩ := urs
  change shape.k = k at hk
  subst hk
  rfl

/-- Deployed acceptance implies halo2's explicit IPA verifier equation. -/
theorem deployedAccepts_verifierEq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (h : DeployedAccepts shape urs hk vk instanceCommitment ps ch) :
    DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch := by
  unfold DeployedAccepts at h
  cases hm : assemble? vk instanceCommitment ps ch with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
      rw [hm] at h
      simp only [] at h
      rw [eval_cast hk m] at h
      have hmeq := assemble?_eq_some vk instanceCommitment ps ch hm
      unfold DeployedIpaVerifierEq
      rw [← deployed_verification_eq (hk ▸ urs.g) urs.w urs.u ps ch
            (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)), ← hmeq]
      exact h

/-- The proof's deployed multiopen commitment over the supplied URS. -/
abbrev deployedCommitment [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : G :=
  multiopenCommitment (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch

end Zcash.Snark
