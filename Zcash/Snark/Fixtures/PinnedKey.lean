import Zcash.Snark.Fixtures.PinnedKeyDescription
import Zcash.Snark.Fixtures.SingleAction.Honest.Fixture
import Zcash.Snark.Verifier.KeyDigest

/-!
# The verifying-key digest, derived from the pinned description

The transcript's first element is the verifying key's digest, `transcript_repr`. This module
derives it instead of taking it from the capture (`capturedVkTranscriptRepr`, also pinned in
`PostNu63.lean`): `keyDigest` over the pinned Post-NU6.3 key description
(`PinnedKeyDescription.lean`, the exact text halo2 hashes) reproduces the captured digest
(`keyDigest_eq_capturedVkTranscriptRepr`), and the description's fields, read back through
`DebugValue`, are the captured key's fields — the domain, column counts, gates, query layouts,
permutation columns, lookups, and both commitment vectors — with the moduli, `extended_k`,
`num_selectors`, `constants`, and `minimum_degree` pinned to the literals the deployed circuit
has, since the verifier's key carries no counterpart for them.

Each family's `Transcript.lean` restates the digest equality at its own captured scalar, and each
`Boundary.lean` then states the fingerprint match with the derived digest opening the transcript
(`nonInteractiveFingerprint_matches_derived_keyDigest`): nothing in the Fiat–Shamir prefix is a
captured value any more. The captured key is the derived key (`Keygen/Certificate.lean`), so
every comparison below transports to `derivedVk`.

What this does not give is cross-key binding: that no other key has this digest is BLAKE2b's
collision resistance, idealized like its randomness (`Capstones/Action.lean`, *Key digest*).
-/

namespace Zcash.Snark.PinnedKey

open Zcash.Snark Zcash.Snark.DebugValue
open CompElliptic.Fields.Pasta

/-- The pinned description, parsed; `pinnedKeyDescription_parses` shows the fallback is unused. -/
def pinned : DebugValue := (parse? pinnedKeyDescription).getD (.atom "")

/-- Recursion budget for reading expressions: one unit per character bounds every nesting. -/
def fuel : ℕ := pinnedKeyDescription.length

/-- The description is one well-formed `Debug` value. -/
theorem pinnedKeyDescription_parses : (parse? pinnedKeyDescription).isSome = true := by
  native_decide

/-- The parse is lossless: rendering it compactly gives back the hashed text. -/
theorem pinned_renderCompact : renderCompact pinned = pinnedKeyDescription := by
  native_decide

/-- **The captured key digest is the digest of the pinned description.** -/
theorem keyDigest_eq_capturedVkTranscriptRepr :
    keyDigest pinnedKeyDescription = Fixture.capturedVkTranscriptRepr := by
  native_decide

/-! ## The pinned fields against the captured key -/

/-- The pinned constraint system. -/
def cs : DebugValue := (pinned.field? "cs").getD (.atom "")

/-- The pinned evaluation domain. -/
def domain : DebugValue := (pinned.field? "domain").getD (.atom "")

/-- The base modulus string names Vesta's base field order. -/
theorem base_modulus_eq :
    (pinned.field? "base_modulus" >>= quotedHexNat?) = some PALLAS_SCALAR_CARD := by
  native_decide

/-- The scalar modulus string names Vesta's scalar field order, the verifier's `F_p`. -/
theorem scalar_modulus_eq :
    (pinned.field? "scalar_modulus" >>= quotedHexNat?) = some PALLAS_BASE_CARD := by
  native_decide

/-- The domain exponent is the captured `k`. -/
theorem domain_k_eq : (domain.field? "k" >>= nat?) = some Fixture.shape.k := by
  native_decide

/-- The extended domain exponent, a keygen constant with no verifier-side counterpart. -/
theorem domain_extended_k_eq : (domain.field? "extended_k" >>= nat?) = some 14 := by
  native_decide

/-- The domain generator is the captured `ω`. -/
theorem domain_omega_eq : (domain.field? "omega" >>= fp?) = some Fixture.vk.omega := by
  native_decide

/-- One fixed commitment per fixed column. -/
theorem num_fixed_columns_eq :
    (cs.field? "num_fixed_columns" >>= nat?) = some Fixture.capturedFixedCommitments.length := by
  native_decide

/-- The advice column count is the captured shape's. -/
theorem num_advice_columns_eq :
    (cs.field? "num_advice_columns" >>= nat?) = some Fixture.shape.numAdviceColumns := by
  native_decide

/-- The instance column count is the captured shape's. -/
theorem num_instance_columns_eq :
    (cs.field? "num_instance_columns" >>= nat?) = some Fixture.shape.numInstanceColumns := by
  native_decide

/-- The selector count, a keygen quantity: selectors are compressed into fixed columns before
the verifier sees the key. -/
theorem num_selectors_eq : (cs.field? "num_selectors" >>= nat?) = some 56 := by
  native_decide

/-- The pinned gates, read as `Expr`, are the captured key's gates. -/
theorem gates_eq : (cs.field? "gates" >>= listOf? (expr? fuel)) = some Fixture.vk.gates := by
  native_decide

/-- The pinned advice queries are the captured advice query layout. -/
theorem advice_queries_eq :
    (cs.field? "advice_queries" >>= listOf? query?) = some Fixture.vk.adviceQueryLayout := by
  native_decide

/-- The pinned instance queries are the captured instance query layout. -/
theorem instance_queries_eq :
    (cs.field? "instance_queries" >>= listOf? query?) = some Fixture.vk.instanceQueryLayout := by
  native_decide

/-- The pinned fixed queries are the captured fixed query layout. -/
theorem fixed_queries_eq :
    (cs.field? "fixed_queries" >>= listOf? query?) = some Fixture.vk.fixedQueryLayout := by
  native_decide

/-- The permutation argument's columns are the captured chunks' columns, in order. -/
theorem permutation_columns_eq :
    ((cs.field? "permutation" >>= (·.field? "columns")) >>= listOf? columnRef?)
      = some (Fixture.vk.permutationChunks.flatten.map Prod.fst) := by
  native_decide

/-- The pinned lookups' input and table expressions are the captured key's. -/
theorem lookups_eq :
    (cs.field? "lookups" >>= listOf? (lookup? fuel))
      = some (List.ofFn fun l : Fin Fixture.shape.numLookups =>
          (Fixture.vk.lookupInputExprs l, Fixture.vk.lookupTableExprs l)) := by
  native_decide

/-- The constants column, a keygen quantity: fixed column 3 holds the circuit's constants. -/
theorem constants_eq : (cs.field? "constants" >>= listOf? columnRef?) = some [.fixed 3] := by
  native_decide

/-- No minimum degree is pinned. -/
theorem minimum_degree_eq : (cs.field? "minimum_degree" >>= atom?) = some "None" := by
  native_decide

/-- The pinned fixed commitments are the captured fixed commitments. -/
theorem fixed_commitments_eq :
    (pinned.field? "fixed_commitments" >>= listOf? point?)
      = some Fixture.capturedFixedCommitments := by
  native_decide

/-- The pinned permutation commitments are the captured permutation commitments. -/
theorem permutation_commitments_eq :
    ((pinned.field? "permutation" >>= (·.field? "commitments")) >>= listOf? point?)
      = some Fixture.capturedPermutationCommonCommitments := by
  native_decide

end Zcash.Snark.PinnedKey
