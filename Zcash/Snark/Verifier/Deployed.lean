import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.Verifier.Instances

/-!
# Halo2-faithful non-interactive verifier entry

This module composes the raw-instance rejection path with the statement-bound Fiat–Shamir
schedule.  Raw public columns are checked before they are committed.  The VK transcript
representation and every resulting instance commitment are then absorbed before proof-controlled
advice commitments and the first challenge. Binding the key here means binding its opaque transcript
representation; this model itself does not connect `vkTranscriptRepr` to the fields of `vk`. At
the captures that connection is checked: `Fixtures/PinnedKey.lean` derives the digest from the
pinned key description (`Verifier/KeyDigest.lean`) and reads the description's fields back against
the key. Its collision resistance — no other key hashing to it — remains below this boundary.

The column commitment operation remains a parameter here.  For Orchard it is instantiated by the
existing Lagrange-basis commitment model; this entry point controls when it may run and how its
outputs enter both the transcript and opening-query assembly. Binding is therefore at commitment
level: Halo2's Lagrange commitment zero-pads columns to the usable length, so raw columns that differ
only by trailing zeros commit and verify identically.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

/-- Checked non-interactive MSM assembly from raw public-instance columns.

This is the generic verifier entry corresponding to Halo2's `verify_proof` control flow: reject
malformed instance shapes, derive their commitments, bind the VK and all instance commitments into
Fiat–Shamir, derive challenges, and finally run the checked MSM assembler. -/
def assembleNonInteractiveInstances? {shape : Shape} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (fs : FiatShamir F G) (vkHash : VerifyingKey shape F G → F) (vk : VerifyingKey shape F G)
    (instances : RawInstances shape F) (commitColumn : List F → G)
    (ps : ProofString shape F G) : Option (Msm shape.k F G) :=
  match validateInstances? vk instances with
  | none => none
  | some valid =>
      let instanceCommitment := valid.commitments commitColumn
      assemble? vk instanceCommitment ps
        (deriveChallengesForStatement fs (vkHash vk) instanceCommitment ps)

theorem assembleNonInteractiveInstances?_eq_none_of_wrong_column_count
    {shape : Shape} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (fs : FiatShamir F G) (vkHash : VerifyingKey shape F G → F) (vk : VerifyingKey shape F G)
    (instances : RawInstances shape F) (commitColumn : List F → G)
    (ps : ProofString shape F G)
    (hcount : ¬ InstancesHaveExpectedColumnCount instances) :
    assembleNonInteractiveInstances? fs vkHash vk instances commitColumn ps = none := by
  simp [assembleNonInteractiveInstances?, validateInstances?, hcount]

theorem assembleNonInteractiveInstances?_eq_none_of_oversized_column
    {shape : Shape} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (fs : FiatShamir F G) (vkHash : VerifyingKey shape F G → F) (vk : VerifyingKey shape F G)
    (instances : RawInstances shape F) (commitColumn : List F → G)
    (ps : ProofString shape F G)
    (hcount : InstancesHaveExpectedColumnCount instances)
    (hfit : ¬ InstanceColumnsFit vk instances) :
    assembleNonInteractiveInstances? fs vkHash vk instances commitColumn ps = none := by
  simp [assembleNonInteractiveInstances?, validateInstances?, hcount, hfit]

/-- Zero-pad a raw instance column on the right to `n` rows (the identity on longer columns). -/
def padColumn {F : Type*} [Zero F] (n : ℕ) (column : List F) : List F :=
  column ++ List.replicate (n - column.length) 0

/-- **Trailing-zero padding invariance.**  When the commitment operation ignores trailing zeros —
Halo2's Lagrange commitment does (`commitInstance_append_replicate_zero`) — this raw verifier
entry cannot distinguish a column from its zero-padding to any length inside the usable rows:
both validate, commit, transcript-bind, and assemble identically.  At the Action circuit with
`n = 10` this is the shorter-column alias stated exactly: a nine-row instance column is accepted
iff the ten-row column extending it with `disableCrossAddress = 0` is.  Row-count validation
cannot exclude the alias — supplying full ten-row columns is a deployed caller obligation,
recorded as `ActionDeploymentInstantiation.instanceColumnsExact`. -/
theorem assembleNonInteractiveInstances?_padColumns
    {shape : Shape} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (fs : FiatShamir F G) (vkHash : VerifyingKey shape F G → F) (vk : VerifyingKey shape F G)
    (instances : RawInstances shape F) (commitColumn : List F → G)
    (ps : ProofString shape F G) (n : ℕ)
    (hpad : ∀ column : List F, commitColumn (padColumn n column) = commitColumn column)
    (hn : n ≤ instanceUsableRows vk)
    (hcols : ∀ p, ∀ column ∈ instances p, column.length ≤ n) :
    assembleNonInteractiveInstances? fs vkHash vk
        (fun p => (instances p).map (padColumn n)) commitColumn ps =
      assembleNonInteractiveInstances? fs vkHash vk instances commitColumn ps := by
  by_cases hcount : InstancesHaveExpectedColumnCount instances
  · have hcount' : InstancesHaveExpectedColumnCount
        (fun p => (instances p).map (padColumn n)) := by
      intro p
      simpa [List.length_map] using hcount p
    have hfit : InstanceColumnsFit vk instances := fun p column =>
      le_trans (hcols p _ (List.get_mem _ _)) hn
    have hfit' : InstanceColumnsFit vk (fun p => (instances p).map (padColumn n)) := by
      intro p column
      have hlt : (column : ℕ) < (instances p).length := by
        simpa [List.length_map] using column.isLt
      have hle : ((instances p)[(column : ℕ)]'hlt).length ≤ n :=
        hcols p _ (List.getElem_mem hlt)
      have hget : ((instances p).map (padColumn n)).get column
          = padColumn n ((instances p)[(column : ℕ)]'hlt) := by
        simp [List.get_eq_getElem]
      rw [hget]
      have hlen : (padColumn n ((instances p)[(column : ℕ)]'hlt)).length = n := by
        simp only [padColumn, List.length_append, List.length_replicate]
        omega
      rw [hlen]
      exact hn
    have hcommit : ∀ p (column : ℕ),
        commitColumn (((instances p).map (padColumn n)).getD column []) =
          commitColumn ((instances p).getD column []) := by
      intro p column
      rcases lt_or_ge column (instances p).length with hcol | hcol
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hcol, Option.map_some, Option.getD_some]
        exact hpad _
      · rw [List.getD_eq_default _ _ (by simpa using hcol),
          List.getD_eq_default _ _ hcol]
    have hfun : ValidatedInstances.commitments
        (vk := vk) ⟨fun p => (instances p).map (padColumn n), hcount', hfit'⟩ commitColumn =
        ValidatedInstances.commitments ⟨instances, hcount, hfit⟩ commitColumn := by
      funext p column
      exact hcommit p column
    simp only [assembleNonInteractiveInstances?, validateInstances?,
      dif_pos hcount, dif_pos hfit, dif_pos hcount', dif_pos hfit']
    rw [hfun]
  · have hcount' : ¬ InstancesHaveExpectedColumnCount
        (fun p => (instances p).map (padColumn n)) := by
      intro h
      exact hcount fun p => by simpa [List.length_map] using h p
    rw [assembleNonInteractiveInstances?_eq_none_of_wrong_column_count
        fs vkHash vk _ commitColumn ps hcount',
      assembleNonInteractiveInstances?_eq_none_of_wrong_column_count
        fs vkHash vk instances commitColumn ps hcount]

end Zcash.Snark
