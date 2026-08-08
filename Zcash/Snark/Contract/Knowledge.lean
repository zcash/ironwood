import Mathlib.Probability.Distributions.Uniform

/-!
# The knowledge-soundness contract

What a circuit's knowledge-soundness endpoint promises, gathered into one record so that it can be
read without reconstructing it from the layers that prove it.

A contract carries four of the six things an auditor must know: the runs the claim quantifies over
together with their law, what acceptance means, what an extraction returns and what a returned
witness certifies, and the event the concrete error bounds. The remaining two are not fields.
Assumptions are the arguments of whatever function builds the contract, so they stay visible in
that signature rather than being summarized here; and the continuation from a circuit witness to a
ledger statement is a separate development.

Nothing in this file proves knowledge soundness. `knowledgeError` and `knowledge_sound` are
supplied by the endpoint that does, and the surrounding fields record what that endpoint's
statement means. The one obligation the record adds is `witness_statement`, without which a
contract would be satisfiable by an extractor that returns junk: a bound on "accepted but returned
nothing" says nothing at all unless returning *something* is known to certify the statement.

The contract deliberately says nothing about completeness. That some run accepts, or that an
honest prover's run extracts, is a separate property; a contract whose `Accepts` holds nowhere
satisfies every field here.
-/

open scoped ENNReal

namespace Zcash.Snark.Contract

universe u v

/-- One circuit's knowledge-soundness contract.

The fields are ordered as they are read: what a run is, when it is accepted, what is extracted
from it, what that extraction certifies, which runs count as failures, and what the failure
probability is bounded by. -/
structure KnowledgeContract where
  /-- One execution of the game the claim is about. -/
  Run : Type u
  /-- The distribution over runs the bound is stated against. -/
  law : PMF Run
  /-- The verifier accepting on this run. -/
  Accepts : Run → Prop
  /-- What a successful extraction returns. Dependent on the run, since the witness is typed by
  the public inputs the adversary selected. -/
  Witness : Run → Type v
  /-- The executable extractor. `none` is extraction failure, and is the only thing the bound is
  about. -/
  extract : (r : Run) → Option (Witness r)
  /-- What a returned witness certifies about the run. -/
  Statement : Run → Prop
  /-- A returned witness entails the statement. This is what makes the bound below a knowledge
  claim rather than a statement about an unconstrained partial function. -/
  witness_statement : ∀ {r : Run}, Witness r → Statement r
  /-- Accepted, yet extraction returned nothing. -/
  failure : Set Run
  /-- `failure` is that event and not some other set. Stated as a field rather than taken as the
  definition so an instance may name the event its proving layer already defines, and discharge
  the identification once. -/
  failure_eq : failure = {r | Accepts r ∧ extract r = none}
  /-- The concrete error the failure event is bounded by. -/
  knowledgeError : ℝ≥0∞
  /-- The claim. -/
  knowledge_sound : law.toOuterMeasure failure ≤ knowledgeError

namespace KnowledgeContract

variable (C : KnowledgeContract)

/-- Accepting a false statement is a knowledge failure.

A returned witness entails the statement, so on a run whose statement is false the extractor must
have returned `none`. -/
theorem acceptFalseStatement_subset_failure :
    {r | C.Accepts r ∧ ¬ C.Statement r} ⊆ C.failure := by
  rw [C.failure_eq]
  rintro r ⟨haccept, hfalse⟩
  refine ⟨haccept, ?_⟩
  -- The only way out of `some` is that the witness would certify the statement we assumed false.
  cases hextract : C.extract r with
  | none => rfl
  | some witness => exact absurd (C.witness_statement witness) hfalse

/-- Ordinary soundness at the same error.

This is the weaker consequence of every contract, and the reason a soundness bound is not worth
advertising separately beside a knowledge bound. -/
theorem acceptFalseStatement_le :
    C.law.toOuterMeasure {r | C.Accepts r ∧ ¬ C.Statement r} ≤ C.knowledgeError :=
  le_trans (MeasureTheory.measure_mono C.acceptFalseStatement_subset_failure) C.knowledge_sound

/-- Membership in the failure event, unfolded. -/
theorem mem_failure_iff {r : C.Run} :
    r ∈ C.failure ↔ C.Accepts r ∧ C.extract r = none := by
  rw [C.failure_eq]; exact Iff.rfl

/-- A run that extracts is not a failure, whether or not it was accepted. -/
theorem not_mem_failure_of_extract_some {r : C.Run} {witness : C.Witness r}
    (hextract : C.extract r = some witness) : r ∉ C.failure := by
  rw [C.mem_failure_iff]
  rintro ⟨-, hnone⟩
  rw [hextract] at hnone
  exact Option.some_ne_none witness hnone

/-- Every accepted run outside the failure event yields a witness, and therefore the statement. -/
theorem statement_of_accepts_of_not_mem_failure {r : C.Run}
    (haccept : C.Accepts r) (hfailure : r ∉ C.failure) : C.Statement r := by
  rw [C.mem_failure_iff] at hfailure
  cases hextract : C.extract r with
  | none => exact absurd ⟨haccept, hextract⟩ hfailure
  | some witness => exact C.witness_statement witness

end KnowledgeContract

end Zcash.Snark.Contract
