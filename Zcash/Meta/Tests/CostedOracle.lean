import Zcash.Snark.Soundness.Action.AdaptiveStatementCost

/-!
# Cost-accounting API regressions

These compile-failure checks pin the audit boundaries that previously admitted forged work
certificates: arbitrary zero-cost lifting, public construction of detached accounting, aggregate
numeric reduction traces, discarded basis/commitment computations, parallel cache recomputation,
and silent discharge of either host-language staging obligation.
-/

namespace Zcash.Snark

/-- error: Unknown constant `Zcash.Snark.CostedLabeledOracleComp.ofLabeled` -/
#guard_msgs (whitespace := lax) in
#check CostedLabeledOracleComp.ofLabeled

/-- error: Unknown constant `Zcash.Snark.CostedLabeledOracleComp.group` -/
#guard_msgs (whitespace := lax) in
#check CostedLabeledOracleComp.group

/-- error: Unknown constant `Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementCostedExecutionCore.mk` -/
#guard_msgs (whitespace := lax) in
#check ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementCostedExecutionCore.mk

/-- error: Unknown identifier `Zcash.Snark.VestaGroupWorkItem` -/
#guard_msgs (whitespace := lax) in
#check Zcash.Snark.VestaGroupWorkItem

/-- error: Unknown constant `Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementCostedExecution.reductionTrace` -/
#guard_msgs (whitespace := lax) in
#check ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementCostedExecution.reductionTrace

/-- error: Unknown constant `Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.costedAdaptiveStatementProgrammedBasis` -/
#guard_msgs (whitespace := lax) in
#check ComputedAdaptiveActionStatementFSFamily.costedAdaptiveStatementProgrammedBasis

/-- error: Unknown constant `Zcash.Snark.ComputedAdaptiveActionStatementFSFamily.costedAdaptiveStatementCanonicalInstances` -/
#guard_msgs (whitespace := lax) in
#check ComputedAdaptiveActionStatementFSFamily.costedAdaptiveStatementCanonicalInstances

/-- error: Unknown constant `Zcash.Snark.CostedVestaComp.auditMsms` -/
#guard_msgs (whitespace := lax) in
#check CostedVestaComp.auditMsms

/-- error: Unknown constant `Zcash.Snark.CostedVestaComp.repeatAudit` -/
#guard_msgs (whitespace := lax) in
#check CostedVestaComp.repeatAudit

/- The certified endpoint has a named, mechanically derived coverage predicate for both composed
adversary/reduction executions. -/
#check ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementProgrammedReductionCoverage
#check ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementExecutionStagingCoverage

/- Total execution work and its single value-threaded program are exposed, but the private
constructor remains inaccessible. -/
#check ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementCostedExecution.groupWork
#check ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementCostedExecution.adversaryProgram
#check ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementCostedExecution.program

/- Closing an oracle path retains its exact annotation log and group work in one proof-carrying
closed program. -/
#check CostedLabeledOracleComp.materializeWithAnnotationsCertified
#check CostedLabeledOracleComp.groupWork_materializeWithAnnotationsCertified
#check ComputedAdaptiveActionStatementFSFamily.AdaptiveStatementAdversaryCostCertificate.certifiedCachedRunProgram_run_eq
#check ComputedAdaptiveActionStatementFSFamily.certifiedCachedKnowledgeExtractorExecutionProgram_groupWork_eq

/-- An executable MSM node must carry its terms; an arbitrary numeric price no longer typechecks. -/
example : VestaGroupOperation := by
  fail_if_success exact .msm 0
  exact .add 0 0

/-- error: Tactic `constructor` failed: target is not an inductive datatype

⊢ (CostedLabeledOracleComp.pure ()).StagedGroupWorkFaithful -/
#guard_msgs (whitespace := lax) in
example : CostedLabeledOracleComp.StagedGroupWorkFaithful
    (CostedLabeledOracleComp.pure () :
      CostedLabeledOracleComp Unit Unit (fun _ => Unit) Unit) := by
  constructor

end Zcash.Snark
