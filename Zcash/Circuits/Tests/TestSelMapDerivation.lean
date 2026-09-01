import Zcash.Snark.Keygen.Pipeline
import Zcash.Circuits.Action.Shape
import Zcash.Circuits.Fixtures.ActionSelMap

/-!
# Cross-check: the derived selector-compression map is the Rust dump

`TopLevelCircuit.selectorMap` — the derivation witness `actionPinnedCs` consumes
(`Zcash/Snark/Fixtures/SingleAction/Honest/VkMatch.lean`) — is computed end to end from
the closed circuit: synthesize mirror → region shapes → V1
floor-planner placement (`FloorPlanner.V1.starts`) → selector activations
(`Layout.activations`) → the `compress_selectors` port (`deriveSelCompressMap`). This
test keeps the Rust-dumped `actionSelMap` as the derivation's cross-checked reference:
the two must stay EQUAL at the Action domain size `n = 2^11`. (`TestFloorPlanner`
separately pins the derived placements against the layout fixture's.)
-/

namespace Zcash.Circuits.Fixtures.Test.SelMapDerivation

open Zcash.Circuits.Action (actionCircuit)

-- The fully derived map (the one wired into `actionPinnedCs`) equals the Rust dump.
#guard actionCircuit.selectorMap == actionSelMap

-- The derived domain exponent (`minimalK`, the keygen fit condition) equals orchard's
-- pinned `K = 11` (`circuit.rs:76`) — so the check above also covers the derived size.
#guard actionCircuit.domainExponent == 11

end Zcash.Circuits.Fixtures.Test.SelMapDerivation
