import Zcash.Snark.Soundness.AGM.Adapter
import Zcash.Snark.Soundness.Forking.Extractor

/-!
# Algebraic prover and forking-certificate interfaces

An AGM prover returns each group element with coefficients over its public basis. This module adds
those coefficients to the types used by the forking extractor.

`AlgebraicProver` is the prefix-determined strategy. `AlgebraicDForkCert` is its explicit
`(3, …, 3)` fork tree. Both erase to the ordinary forking types.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A prefix-determined prover whose group outputs include coefficients over `basis`. -/
inductive AlgebraicProver {ι : Type*} [Fintype ι] (basis : ι → G) : ℕ → Type _ where
  | leaf : F → F → AlgebraicProver basis 0
  | node {d : ℕ} : AlgebraicPoint (F := F) basis → AlgebraicPoint (F := F) basis →
      (F → AlgebraicProver basis d) → AlgebraicProver basis (d + 1)

namespace AlgebraicProver

/-- Erase coefficient vectors to obtain the ordinary prover strategy. -/
def toProver {ι : Type*} [Fintype ι] {basis : ι → G} :
    {d : ℕ} → AlgebraicProver (F := F) basis d → Prover F G d
  | 0, .leaf c f => .leaf c f
  | _ + 1, .node L R cont => .node L.point R.point (fun u => toProver (cont u))

end AlgebraicProver

/-- A fork certificate whose round points include coefficients over one fixed public basis. -/
inductive AlgebraicDForkCert {ι : Type*} [Fintype ι] (basis : ι → G) : ℕ → Type _ where
  | leaf : F → F → AlgebraicDForkCert basis 0
  | node {d : ℕ} : AlgebraicPoint (F := F) basis → AlgebraicPoint (F := F) basis → F → F → F →
      AlgebraicDForkCert basis d → AlgebraicDForkCert basis d → AlgebraicDForkCert basis d →
      AlgebraicDForkCert basis (d + 1)

namespace AlgebraicDForkCert

/-- Erase coefficient vectors to obtain the certificate checked by `DeployedForkValid`. -/
def toDForkCert {ι : Type*} [Fintype ι] {basis : ι → G} :
    {d : ℕ} → AlgebraicDForkCert (F := F) basis d → DForkCert F G d
  | 0, .leaf c f => .leaf c f
  | _ + 1, .node L R u₁ u₂ u₃ c₁ c₂ c₃ =>
      .node L.point R.point u₁ u₂ u₃ (toDForkCert c₁) (toDForkCert c₂) (toDForkCert c₃)

end AlgebraicDForkCert

/-- Acceptance of the ordinary strategy obtained by erasing an algebraic prover's coefficients. -/
def algebraicProverAccept {ι : Type*} [Fintype ι] {basis : ι → G} {d : ℕ}
    (P : AlgebraicProver (F := F) basis d) (g : Fin (2 ^ d) → G)
    (b : Fin (2 ^ d) → F) (U W : G) (z : F) (Pwhole : G) (χ : Fin d → F) : Prop :=
  proverAccept P.toProver g b U W z Pwhole χ

/-- An `Extractable` algebraic strategy has a valid algebraic fork certificate.

The strategy supplies the round-point coefficients. The challenge tree remains existential, so the
computable endpoint takes an `AlgebraicDForkCert` as input instead of choosing one here. -/
theorem algebraicProverAccept_forkValid {ι : Type*} [Fintype ι] {basis : ι → G} {U W : G} {z : F} :
    {d : ℕ} → (P : AlgebraicProver (F := F) basis d) → (g : Fin (2 ^ d) → G) →
      (b : Fin (2 ^ d) → F) → (Pwhole : G) →
      Extractable (algebraicProverAccept P g b U W z Pwhole) →
      ∃ cert : AlgebraicDForkCert (F := F) basis d,
        DeployedForkValid g b U W z Pwhole cert.toDForkCert
  | 0, .leaf c f, g, b, Pwhole, hext => ⟨.leaf c f, hext⟩
  | d + 1, .node L R cont, g, b, Pwhole, hext => by
      obtain ⟨u₁, u₂, u₃, h12, h13, h23, hu₁, hu₂, hu₃, e₁, e₂, e₃⟩ := hext
      obtain ⟨cert₁, hv₁⟩ := algebraicProverAccept_forkValid (cont u₁)
        (foldGens g u₁) (foldGens b u₁)
        (Pwhole + u₁⁻¹ • L.point + u₁ • R.point) e₁
      obtain ⟨cert₂, hv₂⟩ := algebraicProverAccept_forkValid (cont u₂)
        (foldGens g u₂) (foldGens b u₂)
        (Pwhole + u₂⁻¹ • L.point + u₂ • R.point) e₂
      obtain ⟨cert₃, hv₃⟩ := algebraicProverAccept_forkValid (cont u₃)
        (foldGens g u₃) (foldGens b u₃)
        (Pwhole + u₃⁻¹ • L.point + u₃ • R.point) e₃
      exact ⟨.node L R u₁ u₂ u₃ cert₁ cert₂ cert₃,
        h12, h13, h23, hu₁, hu₂, hu₃, hv₁, hv₂, hv₃⟩

end Zcash.Snark
