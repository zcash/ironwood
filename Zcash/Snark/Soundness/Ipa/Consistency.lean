import Zcash.Snark.Soundness.Ipa.Extraction
import Zcash.Snark.Soundness.Ipa.CommitFold

/-!
# Folded IPA generators

`foldGens` is one IPA round's generator fold in the extractor's convention (`gLo + u⁻¹ • gHi`), used by
the IPA soundness layer (`Zcash.Snark.Soundness.Ipa.Soundness`).
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The folded generators for one IPA round, in the extractor's `foldVec` convention (generators by
`u⁻¹`): `gLo + u⁻¹ • gHi`. -/
def foldGens {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (u : F) : Fin (2 ^ k) → G :=
  loHalf g + u⁻¹ • hiHalf g

end Zcash.Snark
