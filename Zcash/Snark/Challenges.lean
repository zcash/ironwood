import Mathlib

/-!
# The verifier's challenges

The verifier collapses its check into one multiscalar multiplication — the fingerprint. As a group
element it is a linear combination of the SRS generators (`g`, `w`, `u`) and the proof's commitment
group elements (the **bases**); its **coefficients** are field elements assembled from the proof's
evaluation scalars and the verifier's challenges. So the challenges are among the fingerprint's
inputs, entering through its coefficients — this module records their values: `θ, β, γ, y, x` (the
main verifier), `x₁…x₄` (the multiopen), `ξ, z`, and the `k` inner-product-argument round challenges
`uⱼ` (the IPA opening).

We do not model the *transcript*. How the challenges are derived — Fiat-Shamir over a Blake2b hash of
the proof so far — is hand-waved (project scope; the deployed non-interactive
derivation is related to the interactive verifier separately). All the fingerprint needs is that the challenges are the
verifier's randomness: free `F_p` variables that the soundness argument (Schwartz–Zippel here,
special-soundness later) quantifies over.
-/

namespace Zcash.Snark

/-- The verifier's challenges, over a field carrier `F`, in squeeze order: `theta` (keeps the lookup
columns linearly independent), `beta`, `gamma`, `y` (keeps the gates linearly independent), and `x`
(the evaluation point) from the main verifier; `x1`–`x4` from the multiopen (compress same-point-set
openings, keep the multi-point quotient terms independent, the opening point, and collapse the
remaining openings); and `xi` (blinds the IPA opening), `z` (binds the inner product to the generator
`u`), and the `k` round challenges `ipaRound` from the IPA opening. -/
structure Challenges (k : ℕ) (F : Type*) where
  theta : F
  beta : F
  gamma : F
  y : F
  x : F
  x1 : F
  x2 : F
  x3 : F
  x4 : F
  xi : F
  z : F
  ipaRound : Fin k → F

end Zcash.Snark
