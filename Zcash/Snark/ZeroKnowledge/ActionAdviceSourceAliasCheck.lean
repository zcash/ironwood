import Zcash.Snark.ZeroKnowledge.ActionAdviceSourceData
import Zcash.Meta.AdviceMapScan

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option stderrAsMessages false
set_option trace.Zcash.adviceMapScan true

/-- The advice-alias scan accepts the source-certified annotations, which is the check behind
every repeated advice write preserving the alias relation, not that statement itself. -/
theorem actionAdviceSource_aliasPlan :
    adviceAliasMapPlan ∅ (adviceAliasAddressData
      (actionAdviceSourceCertificate.annotations.map (fun entry => (entry.1.instruction, entry.2)))) = true := by
  rw [adviceAliasMapPlan_eq_scan]
  check_advice_map_scan

end Zcash.Snark.ZeroKnowledge
