import CompElliptic.Curves.Pasta
import CompElliptic.Curves.Pasta.Fast.Msm
import Clean.Halo2.Keygen.Layout
import Zcash.Circuits.Halo2.CopyLayout
import Zcash.Arithmetic
import Zcash.Arithmetic.Domain
import Zcash.Arithmetic.Fft
import Zcash.Common.ParMap

/-!
# Key-generation commitments

Commitment helpers for circuit-derived fixed columns and permutation
polynomials.
-/

namespace Zcash.Snark.Keygen

open Zcash.Snark
open Zcash.Arithmetic (deltaFp omegaOf)
open Halo2 Halo2.Layout
-- The concrete fast MSM lives in the CompElliptic pin; opening `Curves.Pasta` is what makes its
-- `Fast.Msm.*` spellings resolve here.
open CompElliptic.Curves.Pasta

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-! ## Generalized Lagrange commitment (`poly/commitment.rs:212-216`) -/

/-- Commit to a zero-padded Lagrange-coefficient column against an arbitrary basis with
`Blind::default () = Blind(F::ONE)` (`poly/commitment.rs:212-216`):
`(∑ᵢ coeffsᵢ • basisᵢ) + w` — the same `+ w` blind convention the existing
`commitLagrange` uses, generalized to an arbitrary basis and coefficient list (the
instance-commitment path through `commitLagrange` is deliberately left untouched). -/
def commitLagrangeWith (blind : G) (basis : List G) (coeffs : List Fp) : G :=
  ((List.range coeffs.length).map
    (fun i => (coeffs.getD i 0).val • basis.getD i 0)).sum + blind

/-! ## Commitment helpers over Clean-compiled fixed rows -/

/-- Commit Clean-compiled fixed rows with one task per column. -/
def fixedCommitmentsWith (commit : List Fp → G)
    (rows : List (List Fp)) : List G :=
  rows.parMap commit

/-- Sequential fixed-row commitment variant used by the concrete certificate. -/
def fixedCommitmentsSeqWith (commit : List Fp → G)
    (rows : List (List Fp)) : List G :=
  rows.map commit

omit [AddCommGroup G] [Inhabited G] in
/-- Sequential and parallel fixed-row commitment helpers return the same list. -/
theorem fixedCommitmentsSeqWith_eq (commit : List Fp → G)
    (rows : List (List Fp)) :
    fixedCommitmentsSeqWith commit rows = fixedCommitmentsWith commit rows := by
  simp only [fixedCommitmentsSeqWith, fixedCommitmentsWith, List.parMap_eq_map]

omit [AddCommGroup G] [Inhabited G] in
/-- Pointwise-equal committers give equal sequential fixed commitments. -/
theorem fixedCommitmentsSeqWith_congr {f g : List Fp → G}
    (rows : List (List Fp))
    (h : ∀ row ∈ rows, f row = g row) :
    fixedCommitmentsSeqWith f rows = fixedCommitmentsSeqWith g rows := by
  simp only [fixedCommitmentsSeqWith]
  exact List.map_congr_left h

/-- Commit Clean-compiled fixed rows against a Lagrange basis. -/
def fixedCommitmentsOf (blind : G) (lagrange : List G)
    (rows : List (List Fp)) : List G :=
  fixedCommitmentsWith
    (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow blind lagrange) rows

/-! ## Derived permutation commitments (`plonk/permutation/keygen.rs:102-152`) -/

/-- `[ω^0, ω^1, …, ω^(n−1)]` (`build_vk`'s `omega_powers`, `permutation/keygen.rs:108-116`;
map form rather than iterated multiplication so entries are `getElem`-transparent for the
σ-row identification — `ZMod` powers are binary-fast, so the cost difference is noise). -/
def omegaPowersArr (omega : Fp) (n : ℕ) : Array Fp :=
  (Array.range n).map (omega ^ ·)

/-- `[δ^0, δ^1, …, δ^(m−1)]` (`build_vk`'s `cur *= DELTA`, `permutation/keygen.rs:118-133`;
map form, see `omegaPowersArr`). -/
def deltaPowersArr (delta : Fp) (m : ℕ) : Array Fp :=
  (Array.range m).map (delta ^ ·)

/-- In-range lookup returns the corresponding power of `omega`. -/
@[simp] theorem omegaPowersArr_getElem! (omega : Fp) {n j : ℕ} (hj : j < n) :
    (omegaPowersArr omega n)[j]! = omega ^ j := by
  simp [omegaPowersArr, hj]

/-- In-range lookup returns the corresponding power of `delta`. -/
@[simp] theorem deltaPowersArr_getElem! (delta : Fp) {m j : ℕ} (hj : j < m) :
    (deltaPowersArr delta m)[j]! = delta ^ j := by
  simp [deltaPowersArr, hj]

/-- The per-column permutation polynomials in Lagrange form:
`p_i[j] = deltaomega[i'][j'] = δ^{i'} · ω^{j'}` where `(i', j') = mapping[i][j]`
(`build_vk`, `permutation/keygen.rs:135-146`), over the keygen `Assembly` mapping
(`Assembly::copy` replay, `Layout.runAssembly`) of the derived V1 copy list. -/
def permPolysOf (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    List (List Fp) :=
  let n := 2 ^ k
  let permCols := permColsOf cs
  let copyList := Layout.V1.copyList permCols (FloorPlanner.V1.starts ops) ops
    (constantCopyEntries cs ops)
  let mapping := Layout.runAssembly n permCols.length copyList
  let omegaPows := omegaPowersArr (omegaOf k) n
  let deltaPows := deltaPowersArr deltaFp permCols.length
  (List.range permCols.length).map fun i =>
    (List.range n).map fun j =>
      let pij := (mapping[i]!)[j]!
      deltaPows[pij.1]! * omegaPows[pij.2]!

/-- The derived permutation common commitments at an explicit per-column committer
(see `fixedCommitmentsWith`). -/
def permutationCommitmentsWith (commit : List Fp → G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  -- `parMap`: one task per column (`parMap_eq_map` — evaluation strategy only)
  (permPolysOf k cs ops).parMap commit

/-- Sequential variant of `permutationCommitmentsWith` (see `fixedCommitmentsSeqWith`). -/
def permutationCommitmentsSeqWith (commit : List Fp → G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  (permPolysOf k cs ops).map commit

omit [AddCommGroup G] [Inhabited G] in
/-- Sequential and parallel permutation commitment helpers return the same list. -/
theorem permutationCommitmentsSeqWith_eq (commit : List Fp → G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    permutationCommitmentsSeqWith commit k cs ops
      = permutationCommitmentsWith commit k cs ops := by
  simp only [permutationCommitmentsSeqWith, permutationCommitmentsWith,
    List.parMap_eq_map]

/-- Every permutation polynomial is a full-domain row vector. -/
theorem permPolysOf_mem_length (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    ∀ l ∈ permPolysOf k cs ops, l.length = 2 ^ k := by
  intro l hl
  simp only [permPolysOf, List.mem_map] at hl
  obtain ⟨i, -, rfl⟩ := hl
  simp

omit [AddCommGroup G] [Inhabited G] in
/-- The permutation twin of `fixedCommitmentsSeqWith_congr`. -/
theorem permutationCommitmentsSeqWith_congr {f g : List Fp → G} (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (h : ∀ l : List Fp, l.length = 2 ^ k → f l = g l) :
    permutationCommitmentsSeqWith f k cs ops = permutationCommitmentsSeqWith g k cs ops := by
  simp only [permutationCommitmentsSeqWith]
  exact List.map_congr_left fun c hc => h c (permPolysOf_mem_length k cs ops c hc)

/-- The derived permutation common commitments — `commit_lagrange` of each permutation
polynomial with the default blind (`build_vk`, `permutation/keygen.rs:147-151`;
Pippenger per MSM, `commitLagrangeFastWith_eq` — evaluation strategy only). -/
def permutationCommitmentsOf (blind : G) (lagrange : List G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  permutationCommitmentsWith
    (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow blind lagrange)
    k cs ops

end Zcash.Snark.Keygen
