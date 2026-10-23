import Zcash.Snark.Soundness.Canonical.ConstraintModel

/-! # Permutation arguments across coordinate systems

Chunk flattening and active-row restriction preserve cycles. These coordinate
changes transport the polynomial permutation argument's value equalities without
depending on how a circuit compiler constructs the permutation.
-/

namespace Zcash.Snark.PermutationCoordinates

open Halo2 Equiv

/-- Same-cycle facts transport from the full-domain keygen permutation to its
active-row restriction: the restriction equation pushes powers through the widening,
and widening is injective. -/
theorem sameCycle_restrict_of_widen
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hactive : activeRows ≤ domainSize)
    (fullSigma : Perm (ChunkCell nc domainSize width))
    (sigma : Perm (ChunkCell nc activeRows width))
    (hrestrict : ∀ c : ChunkCell nc activeRows width,
      widenPermutationChunkCell hactive (sigma c) =
        fullSigma (widenPermutationChunkCell hactive c))
    {c d : ChunkCell nc activeRows width}
    (h : fullSigma.SameCycle (widenPermutationChunkCell hactive c)
      (widenPermutationChunkCell hactive d)) :
    sigma.SameCycle c d := by
  classical
  have hpow : ∀ (t : ℕ) (e : ChunkCell nc activeRows width),
      (fullSigma ^ t) (widenPermutationChunkCell hactive e) =
        widenPermutationChunkCell hactive ((sigma ^ t) e) := by
    intro t
    induction t with
    | zero => intro e; rfl
    | succ t ih =>
        intro e
        rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          ← hrestrict e, ih (sigma e)]
  obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
  rw [hpow i c] at hi
  have hcd : (sigma ^ i) c = d :=
    widenPermutationChunkCell_injective hactive hi
  exact ⟨(i : ℤ), by simpa using hcd⟩

/-- Same-cycle facts transport through a conjugating equivalence: the conjugated
permutation's powers are the conjugates of the powers. -/
theorem sameCycle_permCongr_iff {α β : Type*} [DecidableEq α] [Fintype α]
    [DecidableEq β] [Fintype β] (e : α ≃ β) (π : Perm α) (x y : β) :
    (e.permCongr π).SameCycle x y ↔ π.SameCycle (e.symm x) (e.symm y) := by
  have hpow : ∀ (t : ℕ) (z : β),
      ((e.permCongr π) ^ t) z = e ((π ^ t) (e.symm z)) := by
    intro t
    induction t with
    | zero => intro z; simp
    | succ t ih =>
        intro z
        rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          Equiv.permCongr_apply, ih (e (π (e.symm z)))]
        simp
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
    refine ⟨(i : ℤ), ?_⟩
    rw [hpow i x] at hi
    have := congrArg e.symm hi
    simpa using this
  · intro h
    obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
    refine ⟨(i : ℤ), ?_⟩
    have := congrArg e hi
    rw [← hpow i x] at this
    simpa using this

/-- Transport the verifier's cycle-value equality through chunking and active-row restriction. -/
theorem chunkRowValue_eq_of_sameCycle
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (l0 lLast lBlind : CPoly) (p : Fin numProofs) {n m : ℕ}
    (h : ConstraintSatisfaction
      (constraintModelOfResolver (numProofs := numProofs) vk ch poly
        (permutationSetsOfResolver (numProofs := numProofs) vk poly)
        (permutationChunksOfResolver (numProofs := numProofs) vk poly)
        l0 lLast lBlind) n)
    (hdom : ResolverPermutationDomain vk l0 lLast lBlind n m)
    (hcycle : ResolverPermutationCycle vk poly p m)
    (hgood : ResolverPermutationGoodChallenges vk ch poly p m)
    {numCols domainSize : ℕ} (hactive : m ≤ domainSize)
    (sigma : Equiv.Perm (Fin numCols × Fin domainSize))
    (flatten : ResolverPermutationCell vk poly p domainSize ≃
      Fin domainSize × Fin numCols)
    (hrestrict : ∀ c : ResolverPermutationCell vk poly p m,
      widenPermutationChunkCell hactive (hcycle.sigma c) =
        chunkPermutationOfFlat flatten
          ((Equiv.prodComm (Fin numCols) (Fin domainSize)).permCongr
            sigma)
          (widenPermutationChunkCell hactive c))
    (l r : Fin numCols × Fin domainSize) (hflat : sigma.SameCycle l r)
    (cl cr : ResolverPermutationCell vk poly p m)
    (hl : flatten (widenPermutationChunkCell hactive cl) = (l.2, l.1))
    (hr : flatten (widenPermutationChunkCell hactive cr) = (r.2, r.1)) :
    chunkRowValue vk.omega (ResolverPermutationPairs vk poly p)
        cl.1 cl.2.1 cl.2.2 =
      chunkRowValue vk.omega (ResolverPermutationPairs vk poly p)
        cr.1 cr.2.1 cr.2.2 := by
  classical
  -- conjugate to the row-major orientation
  have hswapped :
      (((Equiv.prodComm (Fin numCols) (Fin domainSize)).permCongr
        sigma)).SameCycle (l.2, l.1) (r.2, r.1) := by
    rw [sameCycle_permCongr_iff]
    simpa using hflat
  -- conjugate through the chunk flattening
  have hchunk :
      (chunkPermutationOfFlat flatten
        ((Equiv.prodComm (Fin numCols) (Fin domainSize)).permCongr
          sigma)).SameCycle
        (widenPermutationChunkCell hactive cl)
        (widenPermutationChunkCell hactive cr) := by
    have hcongr :
        chunkPermutationOfFlat flatten
            ((Equiv.prodComm (Fin numCols) (Fin domainSize)).permCongr
              sigma) =
          flatten.symm.permCongr
            ((Equiv.prodComm (Fin numCols) (Fin domainSize)).permCongr
              sigma) := by
      refine Equiv.ext fun c => ?_
      simp [chunkPermutationOfFlat, Equiv.permCongr_apply]
    rw [hcongr, sameCycle_permCongr_iff]
    simpa [hl, hr] using hswapped
  -- restrict to the active rows and read the copy theorem
  exact ConstraintSatisfaction.resolverPermutationCopyConstraints
    vk ch poly l0 lLast lBlind p h hdom hcycle hgood
    (sameCycle_restrict_of_widen hactive _ hcycle.sigma hrestrict hchunk)

/-- Re-widening a row-bounded cell reproduces it. -/
theorem widen_mk_of_lt
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hactive : activeRows ≤ domainSize)
    (x : ChunkCell nc domainSize width) (hx : (x.2.1 : ℕ) < activeRows) :
    widenPermutationChunkCell hactive
        (⟨x.1, ⟨(x.2.1 : ℕ), hx⟩, x.2.2⟩ : ChunkCell nc activeRows width) = x := by
  rcases x with ⟨a, r, col⟩
  rfl

/-- Restrict a full-domain cell permutation to the active rows, given that it maps
active cells to active cells: injectivity survives the restriction, and a finite
injection is a permutation. -/
def restrictActivePerm
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hactive : activeRows ≤ domainSize)
    (π : Perm (ChunkCell nc domainSize width))
    (hpres : ∀ c : ChunkCell nc activeRows width,
      ((π (widenPermutationChunkCell hactive c)).2.1 : ℕ) < activeRows) :
    Perm (ChunkCell nc activeRows width) := by
  let forward : ChunkCell nc activeRows width → ChunkCell nc activeRows width :=
    fun c =>
      ⟨(π (widenPermutationChunkCell hactive c)).1,
        ⟨((π (widenPermutationChunkCell hactive c)).2.1 : ℕ), hpres c⟩,
        (π (widenPermutationChunkCell hactive c)).2.2⟩
  have hforwardWiden (c : ChunkCell nc activeRows width) :
      widenPermutationChunkCell hactive (forward c) =
        π (widenPermutationChunkCell hactive c) := by
    exact widen_mk_of_lt hactive _ (hpres c)
  have hforwardInjective : Function.Injective forward := by
    intro c d h
    apply widenPermutationChunkCell_injective hactive
    apply π.injective
    rw [← hforwardWiden c, ← hforwardWiden d, h]
  have hforwardSurjective : Function.Surjective forward :=
    (Finite.injective_iff_bijective.mp hforwardInjective).2
  have hinversePres (c : ChunkCell nc activeRows width) :
      (((π.symm (widenPermutationChunkCell hactive c)).2.1 : ℕ) < activeRows) := by
    obtain ⟨d, rfl⟩ := hforwardSurjective c
    rw [hforwardWiden d, π.symm_apply_apply]
    exact d.2.1.isLt
  let inverse : ChunkCell nc activeRows width → ChunkCell nc activeRows width :=
    fun c =>
      ⟨(π.symm (widenPermutationChunkCell hactive c)).1,
        ⟨((π.symm (widenPermutationChunkCell hactive c)).2.1 : ℕ), hinversePres c⟩,
        (π.symm (widenPermutationChunkCell hactive c)).2.2⟩
  have hinverseWiden (c : ChunkCell nc activeRows width) :
      widenPermutationChunkCell hactive (inverse c) =
        π.symm (widenPermutationChunkCell hactive c) := by
    exact widen_mk_of_lt hactive _ (hinversePres c)
  exact
    { toFun := forward
      invFun := inverse
      left_inv := fun c => widenPermutationChunkCell_injective hactive (by
        rw [hinverseWiden, hforwardWiden, π.symm_apply_apply])
      right_inv := fun c => widenPermutationChunkCell_injective hactive (by
        rw [hforwardWiden, hinverseWiden, π.apply_symm_apply]) }

/-- The restriction equation of `restrictActivePerm`, by construction. -/
theorem restrictActivePerm_widen
    {nc activeRows domainSize : ℕ} {width : ℕ → ℕ}
    (hactive : activeRows ≤ domainSize)
    (π : Perm (ChunkCell nc domainSize width))
    (hpres : ∀ c : ChunkCell nc activeRows width,
      ((π (widenPermutationChunkCell hactive c)).2.1 : ℕ) < activeRows)
    (c : ChunkCell nc activeRows width) :
    widenPermutationChunkCell hactive (restrictActivePerm hactive π hpres c) =
      π (widenPermutationChunkCell hactive c) :=
  widen_mk_of_lt hactive _ (hpres c)

/-- Chunk cells are determined by their three numeric coordinates. -/
theorem chunkCell_ext {nc m : ℕ} {width : ℕ → ℕ} {x y : ChunkCell nc m width}
    (h1 : (x.1 : ℕ) = (y.1 : ℕ)) (h2 : (x.2.1 : ℕ) = (y.2.1 : ℕ))
    (h3 : (x.2.2 : ℕ) = (y.2.2 : ℕ)) : x = y := by
  rcases x with ⟨a, r, col⟩
  rcases y with ⟨b, s, dol⟩
  simp only at h1 h2 h3
  obtain rfl : a = b := Fin.ext h1
  obtain rfl : r = s := Fin.ext h2
  obtain rfl : col = dol := Fin.ext h3
  rfl

/-- The chunk flattening: halo2 groups the permutation columns into `nc` chunks of
`chunkLen` (the last possibly shorter), so a chunk cell is a `(row, global column)`
pair with `global = chunk · chunkLen + column`. Generic over the chunking law. -/
def chunkFlatten (nc numCols chunkLen m : ℕ) (width : ℕ → ℕ)
    (hcl : 0 < chunkLen) (hcover : numCols ≤ nc * chunkLen)
    (hw : ∀ c : Fin nc, width (c : ℕ) = min chunkLen (numCols - (c : ℕ) * chunkLen)) :
    ChunkCell nc m width ≃ Fin m × Fin numCols where
  toFun cell :=
    (cell.2.1, ⟨(cell.1 : ℕ) * chunkLen + (cell.2.2 : ℕ), by
      have hcol : (cell.2.2 : ℕ) < min chunkLen (numCols - (cell.1 : ℕ) * chunkLen) := by
        rw [← hw cell.1]
        exact cell.2.2.isLt
      have := lt_min_iff.mp hcol
      omega⟩)
  invFun rg :=
    ⟨⟨(rg.2 : ℕ) / chunkLen, by
        have hlt := rg.2.isLt
        by_contra hge
        push Not at hge
        have hmul : nc * chunkLen ≤ (rg.2 : ℕ) / chunkLen * chunkLen :=
          Nat.mul_le_mul_right _ hge
        have hdivle := Nat.div_mul_le_self (rg.2 : ℕ) chunkLen
        omega⟩,
      rg.1,
      ⟨(rg.2 : ℕ) % chunkLen, by
        rw [hw]
        change (rg.2 : ℕ) % chunkLen <
          min chunkLen (numCols - (rg.2 : ℕ) / chunkLen * chunkLen)
        refine lt_min (Nat.mod_lt _ hcl) ?_
        have hlt := rg.2.isLt
        have hdm := Nat.div_add_mod (rg.2 : ℕ) chunkLen
        have hcomm : (rg.2 : ℕ) / chunkLen * chunkLen =
            chunkLen * ((rg.2 : ℕ) / chunkLen) := Nat.mul_comm _ _
        omega⟩⟩
  left_inv cell := by
    rcases cell with ⟨c, i, col⟩
    have hcol : (col : ℕ) < min chunkLen (numCols - (c : ℕ) * chunkLen) := by
      rw [← hw c]
      exact col.isLt
    have hcolcl : (col : ℕ) < chunkLen := lt_of_lt_of_le hcol (min_le_left _ _)
    refine chunkCell_ext ?_ rfl ?_
    · show ((c : ℕ) * chunkLen + (col : ℕ)) / chunkLen = (c : ℕ)
      rw [Nat.mul_comm (c : ℕ) chunkLen, Nat.mul_add_div hcl,
        Nat.div_eq_of_lt hcolcl, Nat.add_zero]
    · show ((c : ℕ) * chunkLen + (col : ℕ)) % chunkLen = (col : ℕ)
      rw [Nat.mul_comm (c : ℕ) chunkLen, Nat.mul_add_mod,
        Nat.mod_eq_of_lt hcolcl]
  right_inv rg := by
    rcases rg with ⟨i, g⟩
    refine Prod.ext_iff.mpr ⟨rfl, Fin.ext ?_⟩
    show (g : ℕ) / chunkLen * chunkLen + (g : ℕ) % chunkLen = (g : ℕ)
    rw [Nat.mul_comm]
    exact Nat.div_add_mod (g : ℕ) chunkLen

@[simp]
theorem chunkFlatten_apply_row
    {nc numCols chunkLen m : ℕ} {width : ℕ → ℕ}
    (hcl : 0 < chunkLen) (hcover : numCols ≤ nc * chunkLen)
    (hw : ∀ c : Fin nc,
      width (c : ℕ) = min chunkLen (numCols - (c : ℕ) * chunkLen))
    (cell : ChunkCell nc m width) :
    (chunkFlatten nc numCols chunkLen m width hcl hcover hw cell).1 =
      cell.2.1 := rfl

@[simp]
theorem chunkFlatten_apply_column
    {nc numCols chunkLen m : ℕ} {width : ℕ → ℕ}
    (hcl : 0 < chunkLen) (hcover : numCols ≤ nc * chunkLen)
    (hw : ∀ c : Fin nc,
      width (c : ℕ) = min chunkLen (numCols - (c : ℕ) * chunkLen))
    (cell : ChunkCell nc m width) :
    ((chunkFlatten nc numCols chunkLen m width hcl hcover hw cell).2 : ℕ) =
      (cell.1 : ℕ) * chunkLen + (cell.2.2 : ℕ) := rfl

@[simp]
theorem chunkFlatten_symm_apply_row
    {nc numCols chunkLen m : ℕ} {width : ℕ → ℕ}
    (hcl : 0 < chunkLen) (hcover : numCols ≤ nc * chunkLen)
    (hw : ∀ c : Fin nc,
      width (c : ℕ) = min chunkLen (numCols - (c : ℕ) * chunkLen))
    (cell : Fin m × Fin numCols) :
    ((chunkFlatten nc numCols chunkLen m width hcl hcover hw).symm cell).2.1 =
      cell.1 := rfl

@[simp]
theorem chunkFlatten_symm_apply_column
    {nc numCols chunkLen m : ℕ} {width : ℕ → ℕ}
    (hcl : 0 < chunkLen) (hcover : numCols ≤ nc * chunkLen)
    (hw : ∀ c : Fin nc,
      width (c : ℕ) = min chunkLen (numCols - (c : ℕ) * chunkLen))
    (cell : Fin m × Fin numCols) :
    (((chunkFlatten nc numCols chunkLen m width hcl hcover hw).symm cell).1 :
        ℕ) *
        chunkLen +
        (((chunkFlatten nc numCols chunkLen m width hcl hcover hw).symm cell).2.2 :
          ℕ) =
      (cell.2 : ℕ) := by
  change (cell.2 : ℕ) / chunkLen * chunkLen +
      (cell.2 : ℕ) % chunkLen = (cell.2 : ℕ)
  rw [Nat.mul_comm]
  exact Nat.div_add_mod (cell.2 : ℕ) chunkLen

end Zcash.Snark.PermutationCoordinates
