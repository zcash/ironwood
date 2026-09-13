import Zcash.Snark.ZeroKnowledge.ActionAdviceSourceData
import Zcash.Meta.AdviceMapScan

namespace Zcash.Snark.ZeroKnowledge
open Halo2 Zcash.Circuits Zcash.Circuits.Action
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option stderrAsMessages false
set_option trace.Zcash.adviceMapScan true

/-- The advice-read support scan accepts the certified annotations.
`adviceSupportMapPlan_causal` carries that to the reading of record: every advice read is
available when the original program executes. -/
theorem actionAdviceSource_readPlan :
    adviceSupportMapPlan actionCircuit.placement ∅
      actionAdviceSourceCertificate.readCertificate.annotations = true := by
  change adviceSupportMapPlan (fun region => actionCircuit.regionStarts.getD region 0) ∅
    actionAdviceSourceCertificate.readCertificate.annotations = true
  rw [actionCircuit_regionStarts_eq_certificate]
  rw [adviceSupportMapPlan_eq_scan]
  check_advice_map_scan

end Zcash.Snark.ZeroKnowledge
