import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Soundness.Ipa.InnerProduct
import Zcash.Common.DiscreteLogRelation

/-!
# The commitment respects the IPA round fold

This closes the consistency seam of the soundness argument: that an accepting transcript folds the
witness the way the extractor assumes. The structural fact is that the polynomial commitment is
compatible with one IPA round — folding the witness by `u⁻¹` and the generators by `u` sends the
parent commitment to the folded one plus the cross terms `L`/`R` the verifier accounts for.

* `commitGen` — the commitment over arbitrary generators (`commit urs = commitGen urs.g`).
* `commitGen_{add,smul}_{left,gen}` — bilinearity in the witness and in the generators.
* `commitGen_round` (proven) — one round's commitment fold, the round's completeness; with
  binding, accepting implies consistent (`accepting_fold_eq`), leaving only binding itself.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The fingerprint/URS commitment is the generator-commitment at the URS generators. -/
theorem commit_eq_commitGen (urs : URS G) (a : Fin (2 ^ urs.k) → F) :
    commit urs a = commitGen urs.g a := rfl





/-- **One IPA round's commitment fold (completeness).** Folding the witness by `u⁻¹` and the generators
by `u` sends the parent commitment to the folded commitment plus the two cross terms `⟨aLo, gHi⟩` and
`⟨aHi, gLo⟩` — exactly the `L`/`R` the verifier accounts for. So the honest witness folds consistently;
a prover response deviating from this fold exhibits a computed discrete-log relation
(`NontrivialDLRelation.ofIpaOpenings`). -/
theorem commitGen_round {m : ℕ} (gLo gHi : Fin m → G) (aLo aHi : Fin m → F) {u : F} (hu : u ≠ 0) :
    commitGen (gLo + u • gHi) (aLo + u⁻¹ • aHi)
      = (commitGen gLo aLo + commitGen gHi aHi)
        + u • commitGen gHi aLo + u⁻¹ • commitGen gLo aHi := by
  simp only [commitGen_add_left, commitGen_smul_left, commitGen_add_gen, commitGen_smul_gen,
    smul_add, smul_smul, inv_mul_cancel₀ hu, one_smul]
  abel

/-- **The binding step: an accepting round response is the true fold.** If the folded-generator
commitment is binding and the prover's response `a'` opens the verifier's folded commitment —
which by `commitGen_round` is exactly what the true fold opens — then `a' = aLo + u⁻¹ • aHi`.
This is the per-node step promoting an accepting transcript to the extractor's fold relation,
leaving binding (DLR hardness) at the folded generators as the only hypothesis. -/
theorem accepting_fold_eq {m : ℕ} (gLo gHi : Fin m → G) (aLo aHi a' : Fin m → F) {u : F} (hu : u ≠ 0)
    (hbind : Function.Injective (commitGen (F := F) (gLo + u • gHi)))
    (haccept : commitGen (gLo + u • gHi) a'
      = (commitGen gLo aLo + commitGen gHi aHi) + u • commitGen gHi aLo + u⁻¹ • commitGen gLo aHi) :
    a' = aLo + u⁻¹ • aHi := by
  apply hbind
  rw [haccept, commitGen_round gLo gHi aLo aHi hu]

/-- `accepting_fold_eq` in the extractor's fold convention (witness by `u`, generators by `u⁻¹`):
an accepting round response equals `foldVec aLo aHi u` — with `aLo := loHalf a`, `aHi := hiHalf a`,
the per-node fold the extractor inverts. Derived at `u⁻¹` via `(u⁻¹)⁻¹ = u`. -/
theorem accepting_fold_eq_foldVec {m : ℕ} (gLo gHi : Fin m → G) (aLo aHi a' : Fin m → F) {u : F}
    (hu : u ≠ 0) (hbind : Function.Injective (commitGen (F := F) (gLo + u⁻¹ • gHi)))
    (haccept : commitGen (gLo + u⁻¹ • gHi) a'
      = (commitGen gLo aLo + commitGen gHi aHi) + u⁻¹ • commitGen gHi aLo + u • commitGen gLo aHi) :
    a' = foldVec aLo aHi u := by
  have key := accepting_fold_eq gLo gHi aLo aHi a' (u := u⁻¹) (inv_ne_zero hu) hbind (by rwa [inv_inv])
  rw [inv_inv] at key
  rwa [foldVec]

/-! ## Binding as a discrete-log-relation hardness assumption

The trust boundary underlying commitment binding: rather than assuming the commitment is binding
outright, binding is modelled as a reduction to discrete-log-relation (DLR) hardness at the URS
generators — the same shape as the binding-signature argument's `NontrivialRelation.ofImbalance`.
`NontrivialDLRelation` carries such a relation as data (breaks as computed data — see the
Ironwood Book,
<https://zcash.github.io/ironwood/formal-verification.html#breaks-as-computed-data>); an
∃-closed relation Prop would be vacuously true, since relations always exist among the
generators of a compressing commitment. `NontrivialDLRelation.ofCollision` computes the
relation from a binding collision, and `.ofIpaOpenings` from two distinct IPA openings of
one commitment — so opening uniqueness holds up to a computed relation. The deployed binding
reduction extends this to the augmented `(g, U, W)` generators
(`Zcash.Snark.Soundness.Deployed.Binding`). Discharging the relation against DLR hardness — the
computational/AGM layer — is outside this
development. -/


/-- A nontrivial discrete-log relation among the URS generators, as data: a nonzero coefficient
vector the generators send to `0`. DLR hardness is the assumption that no feasible adversary can
find one; the reductions below compute it from the corresponding break. -/
structure NontrivialDLRelation (urs : URS G) where
  coeffs : Fin (2 ^ urs.k) → F
  nontrivial : coeffs ≠ 0
  relation : commitGen urs.g coeffs = 0

/-- **The binding reduction, as a computed relation.** A binding collision — two distinct
openings of one commitment — yields the nontrivial discrete-log relation `a − a'` among the URS
generators, exactly as `NontrivialRelation.ofImbalance` closes the binding-signature argument.
DLR hardness closes binding as the contrapositive: the collision is reduced to a relation the
hardness assumption forbids. -/
def NontrivialDLRelation.ofCollision (urs : URS G) {a a' : Fin (2 ^ urs.k) → F}
    (hcol : commit urs a = commit urs a') (hne : a ≠ a') :
    NontrivialDLRelation (F := F) urs :=
  ⟨a - a', sub_ne_zero.mpr hne, by
    rw [commitGen_sub, ← commit_eq_commitGen, ← commit_eq_commitGen, hcol, sub_self]⟩

/-- **IPA opening uniqueness, up to a computed relation.** Two distinct witnesses opening the
same commitment to the same value yield a computed nontrivial discrete-log relation among the
URS generators. Special-soundness extraction therefore pins down the witness up to such a
relation. -/
def NontrivialDLRelation.ofIpaOpenings {urs : URS G} {P : G} {b : Fin (2 ^ urs.k) → F} {v : F}
    {a a' : Fin (2 ^ urs.k) → F} (h : IpaRelation urs P b v a) (h' : IpaRelation urs P b v a')
    (hne : a ≠ a') : NontrivialDLRelation (F := F) urs :=
  .ofCollision urs (h.1.trans h'.1.symm) hne

end Zcash.Snark
