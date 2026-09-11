import Zcash.Circuits.Integration.AssignmentEncoding
import Zcash.Circuits.Integration.CopyPermutation
import Zcash.Circuits.Integration.ExprRich
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Circuits.Integration.PermutationCycle
import Zcash.Circuits.Integration.PolynomialEnvironment
import Zcash.Circuits.Integration.PolynomialQueries
import Zcash.Circuits.Integration.TopLevelConstraintModel
import Zcash.Circuits.Integration.TopLevelCopyConstraints
import Zcash.Circuits.Integration.TopLevelGates
import Zcash.Circuits.Integration.TopLevelInstanceCommitment
import Zcash.Circuits.Integration.TopLevelInterpretation
import Zcash.Circuits.Integration.TopLevelLookups
import Zcash.Circuits.Integration.TopLevelWitness
import Zcash.Circuits.Integration.VerifierCS

/-!
# Clean-to-Ironwood integration

Aggregator for the implementation boundary between Clean formal circuits and the
Ironwood verifier/soundness model: every module of `Zcash/Circuits/Integration/`.

Keep pure verifier-native constraint, permutation, and lookup mathematics in
`Zcash.Snark`; only modules that translate between Clean and Ironwood belong here.
-/
