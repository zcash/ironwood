import Zcash.TrustBoundary
import Zcash.Snark.Fixtures.SingleAction.Honest.TrustBoundary
import Zcash.Snark.Fixtures.SingleAction.Random.TrustBoundary
import Zcash.Snark.Fixtures.MultiAction.Honest.TrustBoundary
import Zcash.Snark.Fixtures.MultiAction.Random.TrustBoundary
import Zcash.Snark.Fixtures.Prover.TrustBoundary
import Zcash.Snark.ZeroKnowledge.TrustBoundary
import Zcash.Snark.ZeroKnowledge.Vesta.TrustBoundary
import Zcash.Snark.ZeroKnowledge.Action.TrustBoundary
import Zcash.Snark.ZeroKnowledge.Action.Certificates.TrustBoundary
import Zcash.Snark.ZeroKnowledge.Zakura.TrustBoundary

/-!
# Endpoint-census completeness at the elaborated environment

This module imports every census file and runs `assert_endpoint_census`
(`Zcash.Meta.EndpointCensus`): each endpoint-named declaration visible here must carry a direct
`assert_axioms`/`assert_computable` pin recorded by an elaborated census entry.  Discovery reads
the environment rather than source text, so a declaration produced by a custom command,
unconventional syntax, or metaprogramming is checked however it was written — the evasions
`scripts/check_endpoint_census.sh`'s line parser cannot see.  The script keeps the wider,
file-tree scope; this target closes the syntax gap inside the census files' import closure.
-/

assert_endpoint_census
