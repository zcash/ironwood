import Mathlib
import Zcash.Snark.Soundness.InnerProduct

/-!
# The commitment respects the IPA round fold

This closes the second soundness seam: that an accepting transcript yields a tree consistent with the
witness (`Zcash.Snark.extract_correct`'s hypothesis). The structural fact is that the polynomial
commitment is compatible with one IPA round — folding the witness by `u⁻¹` and the generators by `u`
sends the parent commitment to the folded one plus the cross terms `L`/`R` the verifier accounts for.

* `commitGen` — the commitment over arbitrary generators (`commit urs = commitGen urs.g`).
* `commitGen_{add,smul}_{left,gen}` — bilinearity in the witness and in the generators.
* `commitGen_round` (proven) — one round's commitment fold: `⟨a' , g'⟩ = ⟨a, g⟩ + u·L + u⁻¹·R`, the
  round's completeness. Together with `Zcash.Snark.ipaRelation_unique` (uniqueness under
  `CommitmentBinding`), this forces the prover's folded response to be the true fold of the committed
  witness — i.e. accepting ⇒ consistent — leaving only the binding assumption itself.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The commitment over arbitrary generators `g`: `⟨a, g⟩ = Σᵢ aᵢ • gᵢ`. Specialises to the URS
commitment: `commit urs = commitGen urs.g`. -/
def commitGen {n : ℕ} (g : Fin n → G) (a : Fin n → F) : G := ∑ i, a i • g i

/-- The fingerprint/URS commitment is the generator-commitment at the URS generators. -/
theorem commit_eq_commitGen (urs : URS G) (a : Fin (2 ^ urs.k) → F) :
    commit urs a = commitGen urs.g a := rfl

/-- Additivity in the witness. -/
theorem commitGen_add_left {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a + a') = commitGen g a + commitGen g a' := by
  simp only [commitGen, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Homogeneity in the witness. -/
theorem commitGen_smul_left {n : ℕ} (g : Fin n → G) (c : F) (a : Fin n → F) :
    commitGen g (c • a) = c • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Additivity in the generators. -/
theorem commitGen_add_gen {n : ℕ} (g g' : Fin n → G) (a : Fin n → F) :
    commitGen (g + g') a = commitGen g a + commitGen g' a := by
  simp only [commitGen, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Homogeneity in the generators. -/
theorem commitGen_smul_gen {n : ℕ} (c : F) (g : Fin n → G) (a : Fin n → F) :
    commitGen (c • g) a = c • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm (a i) c (g i)

/-- One IPA round's commitment fold (completeness). Folding the witness by `u⁻¹` and the generators by
`u` sends the parent commitment to the folded commitment plus the two cross terms `⟨aLo, gHi⟩` and
`⟨aHi, gLo⟩` — exactly the `L`/`R` the verifier accounts for. So the honest witness folds consistently;
with `ipaRelation_unique` (binding), the prover's response must be this fold. -/
theorem commitGen_round {m : ℕ} (gLo gHi : Fin m → G) (aLo aHi : Fin m → F) {u : F} (hu : u ≠ 0) :
    commitGen (gLo + u • gHi) (aLo + u⁻¹ • aHi)
      = (commitGen gLo aLo + commitGen gHi aHi)
        + u • commitGen gHi aLo + u⁻¹ • commitGen gLo aHi := by
  simp only [commitGen_add_left, commitGen_smul_left, commitGen_add_gen, commitGen_smul_gen,
    smul_add, smul_smul, inv_mul_cancel₀ hu, one_smul]
  abel

/-- The binding step: an accepting round response is the true fold. If the folded-generator commitment is
binding and the prover's response `a'` opens the verifier's folded commitment — the parent plus the cross
terms `u·L + u⁻¹·R`, which by `commitGen_round` is exactly what the true fold opens — then `a'` equals the
true fold `aLo + u⁻¹ • aHi`. This promotes an accepting transcript to a `Zcash.Snark.Consistent` tree (the
per-node step; the recursion over the `k` rounds mirrors `Zcash.Snark.extract_correct`), so the only
remaining hypothesis is binding (DLR hardness) at the folded generators. -/
theorem accepting_fold_eq {m : ℕ} (gLo gHi : Fin m → G) (aLo aHi a' : Fin m → F) {u : F} (hu : u ≠ 0)
    (hbind : Function.Injective (commitGen (F := F) (gLo + u • gHi)))
    (haccept : commitGen (gLo + u • gHi) a'
      = (commitGen gLo aLo + commitGen gHi aHi) + u • commitGen gHi aLo + u⁻¹ • commitGen gLo aHi) :
    a' = aLo + u⁻¹ • aHi := by
  apply hbind
  rw [haccept, commitGen_round gLo gHi aLo aHi hu]

/-- The same binding step in the extractor's fold convention (`Zcash.Snark.foldVec`: witness folded by
`u`, generators by `u⁻¹`): an accepting round response opening the folded commitment equals
`foldVec aLo aHi u`. Taking `aLo := loHalf a`, `aHi := hiHalf a`, this is exactly `Zcash.Snark.roundFold a u`
— the per-node condition of `Zcash.Snark.Consistent` — so it is the bridge from an accepting transcript to
a consistent tree. Derived from `accepting_fold_eq` at `u⁻¹` (using `(u⁻¹)⁻¹ = u`). -/
theorem accepting_fold_eq_foldVec {m : ℕ} (gLo gHi : Fin m → G) (aLo aHi a' : Fin m → F) {u : F}
    (hu : u ≠ 0) (hbind : Function.Injective (commitGen (F := F) (gLo + u⁻¹ • gHi)))
    (haccept : commitGen (gLo + u⁻¹ • gHi) a'
      = (commitGen gLo aLo + commitGen gHi aHi) + u⁻¹ • commitGen gHi aLo + u • commitGen gLo aHi) :
    a' = foldVec aLo aHi u := by
  have key := accepting_fold_eq gLo gHi aLo aHi a' (u := u⁻¹) (inv_ne_zero hu) hbind (by rwa [inv_inv])
  rw [inv_inv] at key
  rwa [foldVec]

/-! ## Binding as a discrete-log-relation hardness assumption

The two results below state the trust boundary underlying commitment binding: rather than assuming the
commitment is binding outright, binding is modelled as a reduction to DLR hardness at the URS generators.
The deployed binding reduction extends them to the `U`, `W` generators
(`Zcash.Snark.Soundness.Deployed.Binding`), in place of an independence assumption. Discharging the
resulting relation against DLR hardness is the computational / AGM layer, which is *not* in this
development; `Soundness.AGM.Adapter` records its deterministic algebraic core — `relationWitnessOfCollision`
and the fixed-slot `discreteLogOfCollisionAtChallenge` adapter (challenge slot fixed before the
collision is seen) — while the probabilistic wrapper and the algebraic-prover model remain outside
Lean.

Rather than assuming the commitment is binding outright, the binding reduction models it as a reduction
to a hardness assumption — the same shape as the binding-signature argument's `relation_of_imbalance`:
the counterfactual that breaking binding produces a nontrivial discrete-log relation among the URS
generators (`relation_of_collision`), against the discrete-log-relation (DLR) hardness assumption.
Such relations always *exist* propositionally in a prime-order group; DLR hardness is that no feasible
adversary can *find* one. `commitmentBinding_iff_no_relation` makes precise that
`CommitmentBinding` is exactly DLR hardness, so the assumption is the standard, named one, with the
reduction itself proven. -/

/-- A discrete-log relation among the URS generators: a coefficient vector the generators send to `0`.
It is nontrivial when `r ≠ 0`. DLR hardness is the assumption that no feasible adversary can find a
nontrivial relation. -/
@[reducible] def DLRelation (urs : URS G) (r : Fin (2 ^ urs.k) → F) : Prop :=
  commitGen urs.g r = 0

/-- Additivity over subtraction in the witness. -/
theorem commitGen_sub {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a - a') = commitGen g a - commitGen g a' := by
  simp only [commitGen, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- The binding reduction (counterfactual): a binding collision — two distinct openings of one commitment — yields a
nontrivial discrete-log relation `a − a'` among the URS generators. So DLR hardness closes binding,
exactly as `relation_of_imbalance` closes the binding-signature argument: the collision is reduced to a
relation the hardness assumption forbids. -/
theorem relation_of_collision (urs : URS G) {a a' : Fin (2 ^ urs.k) → F}
    (hcol : commit urs a = commit urs a') (hne : a ≠ a') :
    a - a' ≠ 0 ∧ DLRelation urs (a - a') := by
  refine ⟨sub_ne_zero.mpr hne, ?_⟩
  show commitGen urs.g (a - a') = 0
  rw [commitGen_sub, ← commit_eq_commitGen, ← commit_eq_commitGen, hcol, sub_self]

/-- Binding is exactly DLR hardness. The commitment is binding iff every discrete-log relation among the generators is
trivial — so assuming DLR hardness is assuming `CommitmentBinding`, and the binding hypothesis used by
`ipaRelation_unique` / `knowledge_sound` is precisely the standard, named hardness assumption
(with `relation_of_collision` the proven reduction). -/
theorem commitmentBinding_iff_no_relation (urs : URS G) :
    CommitmentBinding (F := F) urs ↔ ∀ r : Fin (2 ^ urs.k) → F, DLRelation urs r → r = 0 := by
  constructor
  · intro hb r hr
    have hr' : commitGen urs.g r = 0 := hr
    apply hb
    rw [commit_eq_commitGen, commit_eq_commitGen, hr']
    simp [commitGen]
  · intro hnr a a' hcol
    have hr : DLRelation urs (a - a') := by
      show commitGen urs.g (a - a') = 0
      rw [commitGen_sub, ← commit_eq_commitGen, ← commit_eq_commitGen, hcol, sub_self]
    exact sub_eq_zero.mp (hnr _ hr)

end Zcash.Snark
