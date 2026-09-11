import Zcash.Circuits.Integration.CopyPermutation
import Zcash.Circuits.Integration.PermutationCycle
import Zcash.Circuits.Integration.TopLevelCopyConstraints
import Zcash.Circuits.Integration.TopLevelInterpretation
import Zcash.Circuits.Halo2.ConstraintFamilies
import Zcash.Circuits.Halo2.CopyListMembership
import Zcash.Circuits.Integration.ExprRich
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Halo2.FixedConstraints
import Zcash.Snark.Soundness.Multiopen.InstanceColumns
import Zcash.Circuits.Halo2.CopyOperations
import Zcash.Circuits.Halo2.FixedOperations
import Zcash.Circuits.Integration.PermutationColumns
import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Circuits.Integration.PolynomialEnvironment
import Zcash.Circuits.Integration.ResolverQueryEnvironment
import Zcash.Circuits.Halo2.SelectorCompression
import Zcash.Circuits.Integration.AssignmentEncoding
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
