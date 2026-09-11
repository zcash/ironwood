import Zcash.Snark.Soundness.Canonical.PermutationInstantiation
import Zcash.Snark.Soundness.Argument.PermutationConstruction
import Zcash.Snark.Soundness.Pricing.GoodChallenge
import Zcash.Snark.Soundness.Canonical.DomainSelectors
import Zcash.Snark.Verifier.FieldSupport

/-!
# Semantic endpoint for resolver-backed permutation constraints

`PermutationInstantiation` obtains the four polynomial divisibility families from the decoded
commitment resolver.  This file supplies the other half of the call to
`deployed_perm_copy_constraints_all_chunks`: the evaluation-domain facts, the keygen permutation
semantics, and the priced `β`/`γ` exclusions.

The keygen-facing record is intentionally independent of how the witness is obtained.  For the
Action circuit it should be instantiated by the layout replay and VK-matching work: its `sigma`
field is the replayed global cell permutation, and `mapsNames` says that the decoded common
permutation polynomials interpolate the names of the cells to which that permutation sends each
source cell.
-/

namespace Zcash.Snark

open CompPoly CompPoly.CPolynomial
open scoped ENNReal

set_option maxHeartbeats 20000

/-- Flatten a variable-width chunk cell to its global `(row, column)` coordinate.  The width bound
is exactly the verifier invariant that each permutation chunk contains at most `chunkLen` columns. -/
def flattenPermutationChunkCell {nc m chunkLen : ℕ} {width : ℕ → ℕ}
    (hwidth : ∀ c < nc, width c ≤ chunkLen) :
    ChunkCell nc m width → Fin m × Fin (nc * chunkLen)
  | ⟨c, i, j⟩ =>
      (i, ⟨c * chunkLen + j, by
        have hj : (j : ℕ) < chunkLen :=
          lt_of_lt_of_le j.isLt (hwidth c c.isLt)
        calc
          (c : ℕ) * chunkLen + j < (c : ℕ) * chunkLen + chunkLen :=
            Nat.add_lt_add_left hj _
          _ = ((c : ℕ) + 1) * chunkLen := (Nat.succ_mul _ _).symm
          _ ≤ nc * chunkLen :=
            Nat.mul_le_mul_right chunkLen (Nat.succ_le_of_lt c.isLt)⟩)

/-- Flattening is injective even when the final chunk is shorter than `chunkLen`. -/
theorem flattenPermutationChunkCell_injective
    {nc m chunkLen : ℕ} {width : ℕ → ℕ}
    (hwidth : ∀ c < nc, width c ≤ chunkLen) :
    Function.Injective (flattenPermutationChunkCell (m := m) hwidth) := by
  rintro ⟨c, i, j⟩ ⟨c', i', j'⟩ h
  simp only [flattenPermutationChunkCell, Prod.mk.injEq, Fin.mk.injEq] at h
  rcases h with ⟨hi, hoff⟩
  have hj : (j : ℕ) < chunkLen :=
    lt_of_lt_of_le j.isLt (hwidth c c.isLt)
  have hj' : (j' : ℕ) < chunkLen :=
    lt_of_lt_of_le j'.isLt (hwidth c' c'.isLt)
  have hc : (c : ℕ) = c' := by
    rcases lt_trichotomy (c : ℕ) c' with hlt | heq | hgt
    · have hle : (c : ℕ) + 1 ≤ c' := Nat.succ_le_iff.mpr hlt
      have hcol :
          (c : ℕ) * chunkLen + j < (c' : ℕ) * chunkLen + j' := by
        calc
          (c : ℕ) * chunkLen + j < (c : ℕ) * chunkLen + chunkLen :=
            Nat.add_lt_add_left hj _
          _ = ((c : ℕ) + 1) * chunkLen := (Nat.succ_mul _ _).symm
          _ ≤ (c' : ℕ) * chunkLen := Nat.mul_le_mul_right chunkLen hle
          _ ≤ (c' : ℕ) * chunkLen + j' := Nat.le_add_right _ _
      exact False.elim ((Nat.ne_of_lt hcol) hoff)
    · exact heq
    · have hle : (c' : ℕ) + 1 ≤ c := Nat.succ_le_iff.mpr hgt
      have hcol :
          (c' : ℕ) * chunkLen + j' < (c : ℕ) * chunkLen + j := by
        calc
          (c' : ℕ) * chunkLen + j' < (c' : ℕ) * chunkLen + chunkLen :=
            Nat.add_lt_add_left hj' _
          _ = ((c' : ℕ) + 1) * chunkLen := (Nat.succ_mul _ _).symm
          _ ≤ (c : ℕ) * chunkLen := Nat.mul_le_mul_right chunkLen hle
          _ ≤ (c : ℕ) * chunkLen + j := Nat.le_add_right _ _
      exact False.elim ((Nat.ne_of_gt hcol) hoff)
  have hcFin : c = c' := Fin.ext hc
  subst c'
  have hjFin : j = j' := Fin.ext (by simpa using hoff)
  subst j'
  subst i'
  rfl

/-- Embed an active-row chunk cell into the full evaluation-domain cell type. -/
def widenPermutationChunkCell
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hrows : activeRows ≤ domainSize) :
    ChunkCell nc activeRows width → ChunkCell nc domainSize width
  | ⟨chunk, row, column⟩ =>
      ⟨chunk, ⟨row, lt_of_lt_of_le row.isLt hrows⟩, column⟩

/-- Widening an active-row cell into the full evaluation domain loses no coordinate. -/
theorem widenPermutationChunkCell_injective
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hrows : activeRows ≤ domainSize) :
    Function.Injective
      (widenPermutationChunkCell (nc := nc) (width := width) hrows) := by
  rintro ⟨chunk, row, column⟩ ⟨chunk', row', column'⟩ h
  have hchunk : chunk = chunk' := congrArg Sigma.fst h
  subst chunk'
  have hrow : (row : ℕ) = row' :=
    congrArg (fun cell => (cell.2.1 : ℕ)) h
  have hcolumn : (column : ℕ) = column' :=
    congrArg (fun cell => (cell.2.2 : ℕ)) h
  have : row = row' := Fin.ext hrow
  subst row'
  have : column = column' := Fin.ext hcolumn
  subst column'
  rfl

@[simp] theorem widenPermutationChunkCell_fst
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hrows : activeRows ≤ domainSize) (c : ChunkCell nc activeRows width) :
    (widenPermutationChunkCell hrows c).1 = c.1 := rfl

@[simp] theorem widenPermutationChunkCell_row
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hrows : activeRows ≤ domainSize) (c : ChunkCell nc activeRows width) :
    ((widenPermutationChunkCell hrows c).2.1 : ℕ) = c.2.1 := rfl

@[simp] theorem widenPermutationChunkCell_column
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hrows : activeRows ≤ domainSize) (c : ChunkCell nc activeRows width) :
    ((widenPermutationChunkCell hrows c).2.2 : ℕ) = c.2.2 := rfl

/-- Injective names on the flat Halo2 column range induce injective names on the verifier's
variable-width permutation chunks. -/
theorem chunkRowName_injective_of_flat
    {omega delta : Fp} {nc m chunkLen : ℕ} {width : ℕ → ℕ}
    (hwidth : ∀ c < nc, width c ≤ chunkLen)
    (hflat : Function.Injective fun c : Fin m × Fin (nc * chunkLen) =>
      omega ^ (c.1 : ℕ) * delta ^ (c.2 : ℕ)) :
    Function.Injective fun c : ChunkCell nc m width =>
      chunkRowName omega delta chunkLen c.1 c.2.1 c.2.2 := by
  intro c d hname
  apply flattenPermutationChunkCell_injective hwidth
  apply hflat
  simpa [flattenPermutationChunkCell, chunkRowName, rowName] using hname

/-- The standard root-of-unity/coset conditions imply injectivity for all chunked cell names. -/
theorem chunkRowName_injective_of_coset
    {omega delta : Fp} {nc m chunkLen : ℕ} {width : ℕ → ℕ}
    (hwidth : ∀ c < nc, width c ≤ chunkLen)
    (hne : ∀ j : Fin (nc * chunkLen), delta ^ (j : ℕ) ≠ 0)
    (homega : omega ^ m = 1)
    (horder : ∀ i i' : ℕ, i < m → i' < m → omega ^ i = omega ^ i' → i = i')
    (hcoset : ∀ (j j' : Fin (nc * chunkLen)) (t : ℕ),
      delta ^ (j : ℕ) = omega ^ t * delta ^ (j' : ℕ) → j = j') :
    Function.Injective fun c : ChunkCell nc m width =>
      chunkRowName omega delta chunkLen c.1 c.2.1 c.2.2 :=
  chunkRowName_injective_of_flat hwidth
    (name_injective_of_coset (fun j : Fin (nc * chunkLen) => delta ^ (j : ℕ))
      hne homega horder hcoset)

/-- The standard root-of-unity/coset conditions, stated over the actual
variable-width chunk columns rather than the padded `nc * chunkLen` rectangle,
imply injectivity for all chunked cell names. -/
theorem chunkRowName_injective_of_actual_coset
    {omega delta : Fp} {nc m chunkLen : ℕ} {width : ℕ → ℕ}
    (hne : ∀ c : (Σ chunk : Fin nc, Fin (width chunk)),
      delta ^ ((c.1 : ℕ) * chunkLen + (c.2 : ℕ)) ≠ 0)
    (homega : omega ^ m = 1)
    (horder : ∀ i i' : ℕ, i < m → i' < m →
      omega ^ i = omega ^ i' → i = i')
    (hcoset : ∀
      (c d : (Σ chunk : Fin nc, Fin (width chunk))) (t : ℕ),
      delta ^ ((c.1 : ℕ) * chunkLen + (c.2 : ℕ)) =
          omega ^ t *
            delta ^ ((d.1 : ℕ) * chunkLen + (d.2 : ℕ)) →
        c = d) :
    Function.Injective fun c : ChunkCell nc m width =>
      chunkRowName omega delta chunkLen c.1 c.2.1 c.2.2 := by
  have hnames :=
    name_injective_of_coset
      (omega := omega) (u := m)
      (fun c : (Σ chunk : Fin nc, Fin (width chunk)) =>
        delta ^ ((c.1 : ℕ) * chunkLen + (c.2 : ℕ)))
      hne homega horder hcoset
  rintro ⟨chunk, row, column⟩ ⟨chunk', row', column'⟩ heq
  have hpair :
      (row, (⟨chunk, column⟩ :
          Σ current : Fin nc, Fin (width current))) =
        (row', (⟨chunk', column'⟩ :
          Σ current : Fin nc, Fin (width current))) := by
    apply hnames
    simpa [chunkRowName, rowName, Nat.add_comm] using heq
  have hrow : row = row' := congrArg Prod.fst hpair
  have hcolumn :
      (⟨chunk, column⟩ :
          Σ current : Fin nc, Fin (width current)) =
        ⟨chunk', column'⟩ :=
    congrArg Prod.snd hpair
  cases hrow
  cases hcolumn
  rfl


/-- Transport keygen's flat `(row, permutation-column)` permutation through the concrete chunk
layout.  Conjugation preserves the complete cycle structure; no assumption about equal chunk
widths is needed. -/
def chunkPermutationOfFlat
    {nc m widthCount : ℕ} {width : ℕ → ℕ}
    (flatten : ChunkCell nc m width ≃ Fin m × Fin widthCount)
    (sigma : Equiv.Perm (Fin m × Fin widthCount)) :
    Equiv.Perm (ChunkCell nc m width) :=
  (flatten.trans sigma).trans flatten.symm

@[simp] theorem chunkPermutationOfFlat_apply
    {nc m widthCount : ℕ} {width : ℕ → ℕ}
    (flatten : ChunkCell nc m width ≃ Fin m × Fin widthCount)
    (sigma : Equiv.Perm (Fin m × Fin widthCount))
    (c : ChunkCell nc m width) :
    chunkPermutationOfFlat flatten sigma c = flatten.symm (sigma (flatten c)) := rfl

/-- The common permutation polynomial generated for one source column over the full domain.

At row `i`, its interpolation value is the identity name of the cell to which keygen's global
permutation sends `(chunk, i, column)`. This is the mathematical form of Halo2's σ-column
construction; commitment encoding and comparison with a concrete VK are deliberately downstream. -/
def keygenSigmaColumn
    {nc m : ℕ} {width : ℕ → ℕ}
    (omega delta : Fp) (chunkLen : ℕ)
    (sigma : Equiv.Perm (ChunkCell nc m width))
    (chunk : Fin nc) (column : Fin (width chunk)) : CPoly :=
  CPolynomial.CLagrange.interpolate Finset.univ
    (fun i : Fin m => omega ^ (i : ℕ))
    (fun i : Fin m =>
      chunkRowName omega delta chunkLen
        (sigma ⟨chunk, i, column⟩).1
        (sigma ⟨chunk, i, column⟩).2.1
        (sigma ⟨chunk, i, column⟩).2.2)

/-- A generated σ column evaluates on every domain row to the name of the keygen-permuted cell. -/
theorem keygenSigmaColumn_eval
    {nc m : ℕ} {width : ℕ → ℕ}
    {omega delta : Fp} {chunkLen : ℕ}
    (sigma : Equiv.Perm (ChunkCell nc m width))
    (hrows : Function.Injective fun i : Fin m => omega ^ (i : ℕ))
    (chunk : Fin nc) (column : Fin (width chunk)) (i : Fin m) :
    (keygenSigmaColumn omega delta chunkLen sigma chunk column).eval
        (omega ^ (i : ℕ)) =
      chunkRowName omega delta chunkLen
        (sigma ⟨chunk, i, column⟩).1
        (sigma ⟨chunk, i, column⟩).2.1
        (sigma ⟨chunk, i, column⟩).2.2 :=
  by
  rw [eval_toPoly, keygenSigmaColumn, CPolynomial.CLagrange.cinterpolate_eq_interpolate]
  exact Lagrange.eval_interpolate_at_node _ hrows.injOn (Finset.mem_univ i)

/-- Generated σ columns have degree strictly below the full evaluation-domain size. -/
theorem keygenSigmaColumn_natDegree_lt
    {nc m : ℕ} {width : ℕ → ℕ}
    {omega delta : Fp} {chunkLen : ℕ}
    (sigma : Equiv.Perm (ChunkCell nc m width))
    (hrows : Function.Injective fun i : Fin m => omega ^ (i : ℕ))
    (hm : 0 < m) (chunk : Fin nc) (column : Fin (width chunk)) :
    (keygenSigmaColumn omega delta chunkLen sigma chunk column).natDegree < m := by
  have hd :
      (keygenSigmaColumn omega delta chunkLen sigma chunk column).toPoly.degree
        < (m : ℕ) := by
    have h := Lagrange.degree_interpolate_lt
      (s := (Finset.univ : Finset (Fin m)))
      (v := fun i : Fin m => omega ^ (i : ℕ))
      (r := fun i : Fin m =>
        chunkRowName omega delta chunkLen
          (sigma ⟨chunk, i, column⟩).1
          (sigma ⟨chunk, i, column⟩).2.1
          (sigma ⟨chunk, i, column⟩).2.2)
      hrows.injOn
    simpa [keygenSigmaColumn, CPolynomial.CLagrange.cinterpolate_eq_interpolate,
      Finset.card_univ, Fintype.card_fin] using h
  exact natDegree_lt_of_degree_toPoly_lt hm hd

/-- The polynomial pairs, indexed by permutation chunk, selected from one resolver-backed proof. -/
abbrev ResolverPermutationPairs
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) : ℕ → List (CPoly × CPoly) :=
  permutationChunkPairsOfResolver vk poly p

/-- Cells covered by one resolver-backed permutation argument. -/
abbrev ResolverPermutationCell
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) :=
  ChunkCell shape.numPermutationSets m
    (fun c => (ResolverPermutationPairs vk poly p c).length)

namespace VerifyingKey

variable {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) [WellFormed vk]
    (poly : CommitmentId → CPoly) (p : Fin numProofs)

theorem resolverPermutationPairs_length (chunk : Fin shape.numPermutationSets) :
    (ResolverPermutationPairs vk poly p chunk).length =
      min vk.chunkLen (shape.numPermutationColumns - (chunk : ℕ) * vk.chunkLen) := by
  simp only [ResolverPermutationPairs, permutationChunkPairsOfResolver, List.length_map]
  apply WellFormed.permutationChunks_getD_length
  rw [WellFormed.permutationChunks_length (vk := vk)]
  exact chunk.isLt

/-- Field separation and a well-formed chunk layout give unique cell names on
every active prefix. The decoded column polynomials play no role in this fact. -/
theorem permutationNamesInjective [Zcash.Arithmetic.FieldDomainParams Fp] [FieldSupport vk]
    {activeRows : ℕ} (hactive : activeRows ≤ vk.n) :
    Function.Injective fun c : ResolverPermutationCell vk poly p activeRows =>
      chunkRowName vk.omega vk.delta vk.chunkLen c.1 c.2.1 c.2.2 := by
  have hfull : Function.Injective fun c : ResolverPermutationCell vk poly p vk.n =>
      chunkRowName vk.omega vk.delta vk.chunkLen c.1 c.2.1 c.2.2 := by
    apply chunkRowName_injective_of_actual_coset
    · intro j
      exact pow_ne_zero _ vk.delta_ne_zero
    · exact vk.omega_pow_n
    · intro i j hi hj h
      exact vk.omega_isPrimitiveRoot.pow_inj hi hj h
    · intro j j' row hcoset
      have hj := j.2.isLt
      have hj' := j'.2.isLt
      simp only [vk.resolverPermutationPairs_length poly p j.1] at hj
      simp only [vk.resolverPermutationPairs_length poly p j'.1] at hj'
      have hindex := congrArg Fin.val (vk.eq_of_delta_pow_eq_omega_pow_mul
        ⟨(j.1 : ℕ) * vk.chunkLen + (j.2 : ℕ), by omega⟩
        ⟨(j'.1 : ℕ) * vk.chunkLen + (j'.2 : ℕ), by omega⟩ row hcoset)
      have hwidth : (j.2 : ℕ) < vk.chunkLen := lt_of_lt_of_le hj (min_le_left _ _)
      have hwidth' : (j'.2 : ℕ) < vk.chunkLen := lt_of_lt_of_le hj' (min_le_left _ _)
      have hchunk : j.1 = j'.1 := by
        apply Fin.ext
        have hdiv := congrArg (· / vk.chunkLen) hindex
        dsimp only at hdiv
        rw [Nat.mul_comm (j.1 : ℕ), Nat.mul_comm (j'.1 : ℕ),
          Nat.mul_add_div (WellFormed.chunkLen_pos (vk := vk)),
          Nat.mul_add_div (WellFormed.chunkLen_pos (vk := vk)),
          Nat.div_eq_of_lt hwidth, Nat.div_eq_of_lt hwidth', Nat.add_zero,
          Nat.add_zero] at hdiv
        exact hdiv
      obtain ⟨chunk, column⟩ := j
      obtain ⟨chunk', column'⟩ := j'
      dsimp only at hchunk hindex
      subst chunk'
      exact congrArg (Sigma.mk chunk) (Fin.ext (Nat.add_left_cancel hindex))
  intro c d hname
  apply widenPermutationChunkCell_injective hactive
  apply hfull
  simpa only [widenPermutationChunkCell_fst, widenPermutationChunkCell_row,
    widenPermutationChunkCell_column] using hname

end VerifyingKey

/-- VK structure and evaluation-domain facts needed after the polynomial constraints have been
extracted.  These are independent of the proof's committed witness columns. -/
structure ResolverPermutationDomain
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (l0 lLast lBlind : CPoly) (n m : ℕ) : Prop where
  chunkCount : vk.permutationChunks.length = shape.numPermutationSets
  lastRotation :
    vk.omega ^ m = vk.omega ^ (-((vk.blindingFactors : ℤ) + 1))
  root : vk.omega ^ n = 1
  active : ∀ i < m,
    1 - (lLast.eval (vk.omega ^ i) + lBlind.eval (vk.omega ^ i)) ≠ 0
  firstSelector : l0.eval (vk.omega ^ 0) ≠ 0
  lastSelector : lLast.eval (vk.omega ^ m) ≠ 0

/--
Build the permutation-domain record with the canonical first, last-usable, and
blinding-row selectors. The caller retains only the structural VK/domain facts;
all selector evaluations are discharged here.
-/
theorem ResolverPermutationDomain.ofCanonicalSelectors
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G) {n m : ℕ}
    (hn : 0 < n) (hm : m < n)
    (hrows : Function.Injective fun i : Fin n => vk.omega ^ (i : ℕ))
    (hchunkCount : vk.permutationChunks.length = shape.numPermutationSets)
    (hlastRotation :
      vk.omega ^ m = vk.omega ^ (-((vk.blindingFactors : ℤ) + 1)))
    (hroot : vk.omega ^ n = 1) :
    ResolverPermutationDomain vk
      (rowSelectorPolynomial vk.omega ⟨0, hn⟩)
      (rowSelectorPolynomial vk.omega ⟨m, hm⟩)
      (blindSelectorPolynomial vk.omega ⟨m, hm⟩) n m where
  chunkCount := hchunkCount
  lastRotation := hlastRotation
  root := hroot
  active i hi := by
    exact last_add_blind_active ⟨m, hm⟩
      ⟨i, lt_trans hi hm⟩ hi hrows
  firstSelector :=
    firstSelectorPolynomial_nonzero ⟨0, hn⟩ rfl hrows
  lastSelector :=
    lastSelectorPolynomial_nonzero ⟨m, hm⟩ hrows

/-- The semantic content of the common permutation columns.

`mapsNames` connects each decoded common polynomial to the image of that cell under the replayed
keygen permutation. `namesInjective` is the usual root-of-unity/coset property of Halo2's
`ωⁱ · δʲ` cell names. -/
structure ResolverPermutationCycle
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) where
  sigma : Equiv.Perm (ResolverPermutationCell vk poly p m)
  mapsNames : ∀ c : ResolverPermutationCell vk poly p m,
    chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p)
        c.1 c.2.1 c.2.2 =
      chunkRowName vk.omega vk.delta vk.chunkLen
        (sigma c).1 (sigma c).2.1 (sigma c).2.2
  namesInjective :
    Function.Injective fun c : ResolverPermutationCell vk poly p m =>
      chunkRowName vk.omega vk.delta vk.chunkLen c.1 c.2.1 c.2.2

/-- A semantic permutation cycle together with identification of its permutation.
Keeping this package generic prevents concrete circuit definitions from being
normalized merely to elaborate the equality. -/
structure ResolverPermutationCycleWitness
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ)
    (sigma : Equiv.Perm (ResolverPermutationCell vk poly p m)) where
  cycle : ResolverPermutationCycle vk poly p m
  sigma_eq : cycle.sigma = sigma

/-- Construct the resolver's active-row semantic cycle from the full-domain keygen permutation and
its generated common columns.

`hrestrict` says the full keygen permutation preserves the active cells and restricts to `sigma`.
The main equality left to a concrete VK is `hcolumns`: each resolver-selected common polynomial is
the corresponding degree-`< domainSize` generated σ column. -/
def ResolverPermutationCycle.ofKeygenColumns
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → CPoly)
    (p : Fin numProofs) {domainSize activeRows : ℕ}
    (hactive : activeRows ≤ domainSize)
    (fullSigma : Equiv.Perm (ResolverPermutationCell vk poly p domainSize))
    (sigma : Equiv.Perm (ResolverPermutationCell vk poly p activeRows))
    (hrows : Function.Injective fun i : Fin domainSize => vk.omega ^ (i : ℕ))
    (hcolumns : ∀
      (chunk : Fin shape.numPermutationSets)
      (column : Fin (ResolverPermutationPairs vk poly p chunk).length),
      (ResolverPermutationPairs vk poly p chunk)[column].2 =
        keygenSigmaColumn vk.omega vk.delta vk.chunkLen fullSigma chunk column)
    (hrestrict : ∀ c : ResolverPermutationCell vk poly p activeRows,
      widenPermutationChunkCell hactive (sigma c) =
        fullSigma (widenPermutationChunkCell hactive c))
    (hnames : Function.Injective fun c : ResolverPermutationCell vk poly p activeRows =>
      chunkRowName vk.omega vk.delta vk.chunkLen c.1 c.2.1 c.2.2) :
    ResolverPermutationCycle vk poly p activeRows := by
  refine
    { sigma := sigma
      mapsNames := ?_
      namesInjective := hnames }
  rintro ⟨chunk, i, column⟩
  change
    ((ResolverPermutationPairs vk poly p chunk).getD column (0, 0)).2.eval
        (vk.omega ^ (i : ℕ)) =
      chunkRowName vk.omega vk.delta vk.chunkLen
        (sigma ⟨chunk, i, column⟩).1
        (sigma ⟨chunk, i, column⟩).2.1
        (sigma ⟨chunk, i, column⟩).2.2
  rw [List.getD_eq_getElem _ _ column.isLt]
  have hcolumn :
      (ResolverPermutationPairs vk poly p chunk)[column.val].2 =
        keygenSigmaColumn vk.omega vk.delta vk.chunkLen fullSigma chunk column := by
    simpa [List.get_eq_getElem] using hcolumns chunk column
  rw [hcolumn]
  have heval := keygenSigmaColumn_eval
    (delta := vk.delta) (chunkLen := vk.chunkLen) fullSigma hrows chunk column
    ⟨i, lt_of_lt_of_le i.isLt hactive⟩
  let source : ResolverPermutationCell vk poly p activeRows := ⟨chunk, i, column⟩
  have hname := congrArg
    (fun c : ResolverPermutationCell vk poly p domainSize =>
      chunkRowName vk.omega vk.delta vk.chunkLen c.1 c.2.1 c.2.2)
    (hrestrict source)
  calc
    (keygenSigmaColumn vk.omega vk.delta vk.chunkLen fullSigma chunk column).eval
        (vk.omega ^ (i : ℕ)) =
      chunkRowName vk.omega vk.delta vk.chunkLen
        (fullSigma (widenPermutationChunkCell hactive source)).1
        (fullSigma (widenPermutationChunkCell hactive source)).2.1
        (fullSigma (widenPermutationChunkCell hactive source)).2.2 := by
          simpa [source] using heval
    _ = chunkRowName vk.omega vk.delta vk.chunkLen
        (widenPermutationChunkCell hactive (sigma source)).1
        (widenPermutationChunkCell hactive (sigma source)).2.1
        (widenPermutationChunkCell hactive (sigma source)).2.2 := hname.symm
    _ = chunkRowName vk.omega vk.delta vk.chunkLen
        (sigma ⟨chunk, i, column⟩).1
        (sigma ⟨chunk, i, column⟩).2.1
        (sigma ⟨chunk, i, column⟩).2.2 := by simp [source]

/-- The polynomial in `γ` whose non-roots let the grand-product identity recover the multiset of
`(value, name)` pairs.  Its coefficients are fixed after `β` is squeezed. -/
def resolverPermutationGammaDifference
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) : CPoly :=
  linProdDiff
    ((chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))).map
        (fun q => q.1 + q.2 * ch.beta))
    ((chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)).map
        (fun q => q.1 + q.2 * ch.beta))

/-- The part of a source-cell permutation factor fixed before `γ` is squeezed. -/
def resolverPermutationFactorOffset
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ)
    (cell : ResolverPermutationCell vk poly p m) : Fp :=
  chunkRowValue vk.omega (ResolverPermutationPairs vk poly p)
      cell.1 cell.2.1 cell.2.2
    + ch.beta * chunkRowName vk.omega vk.delta vk.chunkLen
      cell.1 cell.2.1 cell.2.2

/-- Values of `γ` that make at least one source-cell permutation factor vanish. -/
def resolverPermutationZeroFactorBadSet
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) : Finset Fp :=
  additiveZeroBadSet (resolverPermutationFactorOffset vk ch poly p m)

/-- A zero source-cell factor is exactly membership in its schedule-correct `γ` bad set. -/
theorem mem_resolverPermutationZeroFactorBadSet_iff
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) :
    ch.gamma ∈ resolverPermutationZeroFactorBadSet vk ch poly p m ↔
      ∃ cell : ResolverPermutationCell vk poly p m,
        chunkRowValue vk.omega (ResolverPermutationPairs vk poly p)
            cell.1 cell.2.1 cell.2.2
          + ch.beta * chunkRowName vk.omega vk.delta vk.chunkLen
            cell.1 cell.2.1 cell.2.2
          + ch.gamma = 0 := by
  exact mem_additiveZeroBadSet_iff
    (resolverPermutationFactorOffset vk ch poly p m) ch.gamma

/-- The residual zero-factor exclusion costs at most one `γ` value per active permutation cell. -/
theorem uniformChallenge_resolverPermutationZeroFactorBadSet
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) :
    uniformChallenge.toOuterMeasure
        (resolverPermutationZeroFactorBadSet vk ch poly p m)
      ≤ (Fintype.card (ResolverPermutationCell vk poly p m) : ℝ≥0∞)
          / (Fintype.card Fp : ℝ≥0∞) :=
  uniformChallenge_additiveZeroBadSet
    (resolverPermutationFactorOffset vk ch poly p m)

/-- The complete `γ` exclusion: roots needed for multiset recovery together with the individual
source-cell factors that must stay nonzero while propagating equality around a cycle. -/
def resolverPermutationGammaBadSet
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) : Finset Fp :=
  szBadSet (resolverPermutationGammaDifference vk ch poly p m) ∪
    resolverPermutationZeroFactorBadSet vk ch poly p m

/-- The combined `γ` exclusion has the sum of the Schwartz–Zippel and active-cell budgets. -/
theorem uniformChallenge_resolverPermutationGammaBadSet
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) :
    uniformChallenge.toOuterMeasure
        (resolverPermutationGammaBadSet vk ch poly p m)
      ≤ ((resolverPermutationGammaDifference vk ch poly p m).natDegree +
            Fintype.card (ResolverPermutationCell vk poly p m) : ℕ) /
          (Fintype.card Fp : ℝ≥0∞) := by
  refine le_trans
    (uniformChallenge_szBadSet_union
      (resolverPermutationGammaDifference vk ch poly p m)
      (resolverPermutationZeroFactorBadSet vk ch poly p m)) ?_
  gcongr
  exact_mod_cast additiveZeroBadSet_card_le
    (resolverPermutationFactorOffset vk ch poly p m)

/-- The challenge exclusions used both to recover the multiset of `(value, name)` pairs and to
propagate equality around its cycles.  They are kept separate from VK semantics because the
random-oracle bad-set accounting, rather than key generation, supplies them. -/
structure ResolverPermutationGoodChallenges
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (p : Fin numProofs) (m : ℕ) : Prop where
  gamma : ch.gamma ∉ resolverPermutationGammaBadSet vk ch poly p m
  beta : ∀ j, ch.beta ∉ szBadSet (pairProdDiffCoeff
    (chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p)))
    (chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)) j)

/-- Resolver-backed full constraint satisfaction enforces equality on every replayed keygen
permutation cycle. The zero-factor branch is excluded by the separately priced active-cell
component of `ResolverPermutationGoodChallenges.gamma`.

The proof does no new algebra: it joins the polynomial half from
`ConstraintSatisfaction.resolverPermutationConstraints` to the domain, keygen-semantic, and
good-challenge halves at `deployed_perm_copy_constraints_all_chunks`. -/
theorem ConstraintSatisfaction.resolverPermutationCopyConstraints
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (l0 lLast lBlind : CPoly)
    (p : Fin numProofs) {n m : ℕ}
    (h : ConstraintSatisfaction
      (constraintModelOfResolver (numProofs := numProofs) vk ch poly
        (permutationSetsOfResolver (numProofs := numProofs) vk poly)
        (permutationChunksOfResolver (numProofs := numProofs) vk poly)
        l0 lLast lBlind) n)
    (hdom : ResolverPermutationDomain vk l0 lLast lBlind n m)
    (hcycle : ResolverPermutationCycle vk poly p m)
    (hgood : ResolverPermutationGoodChallenges vk ch poly p m)
    {c d : ResolverPermutationCell vk poly p m}
    (hcd : hcycle.sigma.SameCycle c d) :
    chunkRowValue vk.omega (ResolverPermutationPairs vk poly p)
        c.1 c.2.1 c.2.2 =
      chunkRowValue vk.omega (ResolverPermutationPairs vk poly p)
        d.1 d.2.1 d.2.2 := by
  by_cases hnonempty : 0 < shape.numPermutationSets
  · have hconstraints :=
      h.resolverPermutationConstraints vk ch poly l0 lLast lBlind p
        hnonempty hdom.chunkCount hdom.lastRotation
    have hresult := deployed_perm_copy_constraints_all_chunks
      vk.omega ch.beta ch.gamma vk.delta vk.chunkLen
      (fun chunk => poly (.permProduct p chunk))
      (ResolverPermutationPairs vk poly p)
      l0 lLast lBlind hnonempty hcycle.sigma
      hconstraints.step hconstraints.chain hconstraints.start hconstraints.finish
      (by
        intro i
        rw [← pow_mul, Nat.mul_comm, pow_mul, hdom.root, one_pow])
      hdom.active hdom.firstSelector hdom.lastSelector
      hcycle.mapsNames hcycle.namesInjective
      (fun hmem => hgood.gamma (Finset.mem_union_left _ hmem)) hgood.beta hcd
    rcases hresult with heq | hzero
    · exact heq
    · apply False.elim
      apply hgood.gamma
      apply Finset.mem_union_right
      rw [mem_resolverPermutationZeroFactorBadSet_iff]
      rcases hzero with ⟨chunk, hchunk, i, hi, j, hj, hfactor⟩
      exact ⟨⟨⟨chunk, Finset.mem_range.mp hchunk⟩,
        ⟨⟨i, Finset.mem_range.mp hi⟩, ⟨j, Finset.mem_range.mp hj⟩⟩⟩, hfactor⟩
  · exact False.elim (by
      have hc := c.1.isLt
      omega)

end Zcash.Snark
