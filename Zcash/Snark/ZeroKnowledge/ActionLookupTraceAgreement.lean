import Zcash.Snark.ZeroKnowledge.ActionSourceLookupTrace
import Zcash.Snark.ZeroKnowledge.ActionLookupSourceCertificate

/-!
# The compositional trace and the certified walk agree

Transitional corroboration, kept for one commit. The two derivations of the Action circuit's
lookup labels are independent: the certificate replays the circuit's own operation stream
through `certify_source_list`, recording an equality per reduction step across the opacity
barrier; the compositional trace is assembled from the gadgets' configured traces and crosses
that barrier once, through the recorded implementation equation. This checks that they describe
the same 2,424 labels.

The check evaluates both sides and compares them. It must not be derived from the certificate's
own `source_eq`, which would make it a consequence of one side rather than a comparison of two.

Once the coverage proof reads its labels from the compositional trace, the certificate and this
module disappear together.
-/

namespace Zcash.Snark.ZeroKnowledge

open Halo2 Zcash.Circuits Zcash.Circuits.Action

set_option maxRecDepth 50000
set_option maxHeartbeats 0

/-- Placing the compositional trace yields exactly the entries the certified walk records. -/
theorem actionSourceLookupTrace_placed_eq_certificate :
    placeSelectorTrace actionRegionStartsCertificate (actionSourceLookupTrace actionConfig) 0 =
      actionLookupActivationSourceCertificate.entries := by
  decide

end Zcash.Snark.ZeroKnowledge
