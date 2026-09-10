import Zcash.Circuits.Integration.CopyPermutation
import Zcash.Circuits.Integration.PermutationCycle
import Zcash.Circuits.Integration.TopLevelCopyConstraints
import Zcash.Circuits.Integration.TopLevelInterpretation
import Zcash.Circuits.Integration.CircuitIntegration
import Zcash.Circuits.Integration.CircuitSatisfaction
import Zcash.Circuits.Integration.CopyListMembership
import Zcash.Circuits.Integration.ExprRich
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Integration.FixedLayout
import Zcash.Circuits.Integration.InstanceColumns
import Zcash.Circuits.Integration.LookupProjection
import Zcash.Circuits.Integration.LookupSelectorRows
import Zcash.Circuits.Integration.OperationCopies
import Zcash.Circuits.Integration.OperationFixed
import Zcash.Circuits.Integration.OperationGates
import Zcash.Circuits.Integration.OperationLookups
import Zcash.Circuits.Integration.PermutationColumns
import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Circuits.Integration.PermutationReplay
import Zcash.Circuits.Integration.PolynomialEnvironment
import Zcash.Circuits.Integration.ResolverGates
import Zcash.Circuits.Integration.ResolverQueryEnvironment
import Zcash.Circuits.Integration.SelectorCoherence
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Circuits.Integration.TopLevelBridge
import Zcash.Circuits.Integration.TopLevelCircuit
import Zcash.Circuits.Integration.TopLevelCoherence
import Zcash.Circuits.Integration.TopLevelConstraintModel
import Zcash.Circuits.Integration.TopLevelWitness
import Zcash.Circuits.Integration.TopLevelGates
import Zcash.Circuits.Integration.TopLevelInstanceCommitment
import Zcash.Circuits.Integration.TopLevelLookups

/-!
# Clean-to-Ironwood integration

Aggregator for the implementation boundary between Clean formal circuits and the
Ironwood verifier/soundness model: every module of `Zcash/Circuits/Integration/`.

Keep pure verifier-native constraint, permutation, and lookup mathematics in
`Zcash.Snark`; only modules that translate between Clean and Ironwood belong here.
-/
