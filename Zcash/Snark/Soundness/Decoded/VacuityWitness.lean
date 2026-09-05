import Zcash.Snark.Soundness.Decoded.Vesta

/-!
# Why the break must travel as data: the vacuity witness at Vesta

The breaks-as-computed-data discipline (`Zcash.Security.Common.RandomOracle`,
`Zcash.Common.DiscreteLogRelation`) rests on a claim the development so far states only in prose:
in a prime-order group a nontrivial discrete-log relation among *any* generators already exists, so
an ∃-closed `Prop` recording one is simply true and a theorem concluding `statement ∨ ∃-relation`
carries no information about the statement.

This module discharges that claim at the concrete carrier, so the discipline rests on a theorem
rather than on a remark. `nonempty_nontrivialRelation_vesta` exhibits a relation among arbitrary
Vesta generators using nothing but the group order — no transcript, no verifying key, no acceptance
hypothesis.

## What it implies for the soundness endpoints

The endpoints conclude `statement ⊕' NontrivialRelation …`. Read against this theorem the two
tiers of census pin say sharply different things:

* An endpoint pinned with `assert_computable` is a plain `def`, so its relation coefficients are
  terms of its inputs. `Classical.choice` cannot have supplied them — that is exactly what the
  plain-`def` check in `Zcash.Meta.AxiomCheck` rejects — and this theorem is no help in
  discharging it. Such an endpoint genuinely exhibits an extractor.
* An endpoint that is a `noncomputable def` carries no such guarantee. Because the right summand is
  inhabited unconditionally, `PSum.inr (Classical.arbitrary _)` has its type; the acceptance
  hypotheses are not forced by the *statement*, only honoured by the proof that happens to be
  written. Its `assert_axioms` pin bounds the trusted base and says nothing about extraction.

So this is the anti-vacuity instrument for the endpoint census: it identifies precisely which pin
carries the extraction claim, and it is the reason the `⊕'`-with-data shape is not by itself
sufficient. The member-decode route starts from explicit AGM coordinates and keeps every relation
branch as computed data.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder card_Fp)

open CompElliptic.Curves.Pasta

/-- **A nontrivial relation among arbitrary Vesta generators, from the group order alone.**

`VestaG` has prime order `|Fp|`, so for `w ≠ 0` the map `c ↦ c • w` is injective between types of
equal cardinality, hence surjective: some `c` sends `w` to `u`, and `(0, 1, -c)` is a nontrivial
relation. For `w = 0` the coefficients `(0, 0, 1)` already are one.

The generators are unconstrained — in particular this applies to a captured fixture's URS. Nothing
about honest generation, a transcript, or verifier acceptance is used, which is the whole point:
see the module docstring for what this does and does not say about the endpoints. -/
theorem nonempty_nontrivialRelation_vesta {n : ℕ}
    (g : Fin n → VestaG) (u w : VestaG) :
    Nonempty (Zcash.AugmentedRelationWitness (F := Fp) g u w) := by
  classical
  by_cases hw : w = 0
  · exact ⟨Zcash.NontrivialRelation.ofParts 0 ![0, 1]
      (Or.inr (Function.ne_iff.mpr ⟨1, by simp⟩))
      (by simp [hw, commitGen, Fin.sum_univ_two])⟩
  · have hinj : Function.Injective (fun c : Fp => c • w) := by
      intro c c' h
      by_contra hne
      have hd : c - c' ≠ 0 := sub_ne_zero.mpr hne
      have hzero : (c - c') • w = 0 := by
        have hcc : c • w = c' • w := h
        rw [sub_smul, hcc, sub_self]
      refine hw ?_
      calc w = (c - c')⁻¹ • ((c - c') • w) := by rw [inv_smul_smul₀ hd]
        _ = 0 := by rw [hzero, smul_zero]
    letI : Fintype VestaG := Fintype.ofFinite VestaG
    have hcard : Fintype.card Fp = Fintype.card VestaG := by
      rw [card_Fp, ← Nat.card_eq_fintype_card, Vesta.card_eq]
    have hbij : Function.Bijective (fun c : Fp => c • w) :=
      (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩
    obtain ⟨c, hc⟩ := hbij.2 u
    have hcw : c • w = u := hc
    exact ⟨Zcash.NontrivialRelation.ofParts 0 ![1, -c]
      (Or.inr (Function.ne_iff.mpr ⟨0, by simp⟩))
      (by simp [neg_smul, hcw, commitGen, Fin.sum_univ_two])⟩

end Zcash.Snark
