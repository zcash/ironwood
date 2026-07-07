import Zcash.Snark.Soundness.IpaSoundness
import Zcash.Snark.Verifier.Ipa

/-!
# The deployed flattened IPA MSM unfolds into the recursive generator fold

`eval_assembleFinalMsm` gives the flattened deployed verification equation; `ipa_soundV` proves soundness of
the recursive verifier. This module connects their generator terms, so the structural correspondence between
the flattened MSM and the recursive fold is established here rather than left to the Fiat–Shamir bridge.

The key is the `compute_s` correspondence: the deployed `g`-scalars `computeS u init` halve at each round
exactly as `commitGen_append` splits a commitment, so `commitGen g (sFun u init)` folds recursively with the
generator step `loHalf g + uⱼ • hiHalf g`. That step is `Consistency.foldGens` at the inverted challenge
(`foldGens g (uⱼ⁻¹) = loHalf g + uⱼ • hiHalf g`), which reconciles the deployed `u`-convention with
`ipa_soundV`'s `u⁻¹`-convention.

* `computeS_cons` — `computeS (uⱼ :: rest) = computeS rest ++ (computeS rest).map (· * uⱼ)`.
* `computeS_length` — `|computeS u init| = 2 ^ |u|`.
* `sFun` — the deployed `g`-scalar vector as a `Fin (2 ^ k) → F` function (`computeS` indexed by `getD`).
* `foldAll` / `deployed_gterm_foldAll` — the `g`-term of `eval_assembleFinalMsm` is `[-c]·G'₀`, the folded
  generator.
-/

namespace Zcash.Snark

variable {F : Type*} [Field F]

/-- The round recursion of `computeS` (in the `foldr` direction): one challenge doubles the vector, the new
half scaled by `uⱼ`. From `computeS u init = u.reverse.foldl …`, via `reverse_cons` + `foldl_append`. -/
theorem computeS_cons (uⱼ : F) (rest : List F) (init : F) :
    computeS (uⱼ :: rest) init = computeS rest init ++ (computeS rest init).map (· * uⱼ) := by
  simp only [computeS, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `computeS u init` has `2 ^ |u|` entries (it doubles each round). -/
theorem computeS_length (u : List F) (init : F) : (computeS u init).length = 2 ^ u.length := by
  induction u generalizing init with
  | nil => simp [computeS]
  | cons a t ih => rw [computeS_cons, List.length_append, List.length_map, ih, List.length_cons]; ring

/-- The deployed `g`-scalar vector `computeS u init` as a `Fin (2 ^ |u|) → F` function, defined
recursively so that it `append`s its two halves — making `loHalf`/`hiHalf` definitional
(`loHalf_append`/`hiHalf_append`) and the commitment recursion clean. `sFun_getD` ties it back to the
deployed `getD`-indexed form used in `eval_assembleFinalMsm`. -/
def sFun : (u : List F) → F → Fin (2 ^ u.length) → F
  | [], init => fun _ => init
  | uⱼ :: rest, init => append (sFun rest init) (uⱼ • sFun rest init)

/-- `getD` commutes with a scalar-multiply map (default `0` maps to `0 * c = 0`). -/
theorem getD_map_mul (l : List F) (c : F) (j : ℕ) :
    (l.map (· * c)).getD j 0 = l.getD j 0 * c := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> simp

/-- `sFun` agrees with the deployed `getD`-indexed `computeS`. -/
theorem sFun_getD (u : List F) (init : F) (i : Fin (2 ^ u.length)) :
    sFun u init i = (computeS u init).getD i.val 0 := by
  induction u with
  | nil => simp [sFun, computeS]
  | cons uⱼ rest ih =>
    have hlen : (computeS rest init).length = 2 ^ rest.length := computeS_length rest init
    rw [computeS_cons, sFun]
    by_cases h : i.val < 2 ^ rest.length
    · rw [append, dif_pos h, ih, List.getD_append _ _ _ _ (by rw [hlen]; exact h)]
    · rw [append, dif_neg h, Pi.smul_apply, ih, smul_eq_mul,
        List.getD_append_right _ _ _ _ (by rw [hlen]; omega), getD_map_mul, hlen]
      ring

variable {G : Type*} [AddCommGroup G] [Module F G]

/-- The deployed `g`-term of `eval_assembleFinalMsm` (`∑ i, (computeS u init).getD i • g i`) is the
commitment of the `s`-vector: `commitGen g (sFun u init)`. (From `sFun_getD`.) -/
theorem gterm_eq (u : List F) (init : F) (g : Fin (2 ^ u.length) → G) :
    (∑ i, (computeS u init).getD i.val 0 • g i) = commitGen g (sFun u init) := by
  simp only [commitGen]
  exact Finset.sum_congr rfl (fun i _ => by rw [sFun_getD])

/-- The `s`-vector commitment recurses by the round challenge: the head challenge `uⱼ` combines the two
generator halves (the deployed `u`-convention). `commitGen_append` + `commitGen_smul_left` on `sFun`'s
definitional `append`. -/
theorem commitGen_sFun_cons (uⱼ init : F) (rest : List F) (g : Fin (2 ^ (rest.length + 1)) → G) :
    commitGen g (sFun (uⱼ :: rest) init)
      = commitGen (loHalf g) (sFun rest init) + uⱼ • commitGen (hiHalf g) (sFun rest init) := by
  rw [sFun, commitGen_append, commitGen_smul_left]

/-- The deployed `s`-vector commitment is one `foldGens` step (at the inverted challenge). This is the
convention reconciliation: the deployed flattening (`computeS` with `uⱼ`) folds the generators by
`foldGens g uⱼ⁻¹ = loHalf g + uⱼ • hiHalf g` — exactly `ipa_soundV`'s `foldGens` at `uⱼ⁻¹`. So the deployed
`g`-term unfolds into the same recursion `ipa_soundV` runs on. -/
theorem sFun_fold (uⱼ init : F) (rest : List F) (g : Fin (2 ^ (rest.length + 1)) → G) :
    commitGen g (sFun (uⱼ :: rest) init) = commitGen (foldGens g uⱼ⁻¹) (sFun rest init) := by
  rw [commitGen_sFun_cons, foldGens, commitGen_add_gen, commitGen_smul_gen, inv_inv]

/-- The full generator fold: fold `g` by `foldGens` at the inverted challenges down to a single generator. -/
def foldAll : (u : List F) → (Fin (2 ^ u.length) → G) → (Fin (2 ^ 0) → G)
  | [], g => g
  | uⱼ :: rest, g => foldAll rest (foldGens g uⱼ⁻¹)

/-- The deployed `g`-term is `init` times the fully-folded generator. Iterating `sFun_fold`:
`commitGen g (sFun u init) = init • foldAll u g 0`. So `eval_assembleFinalMsm`'s `computeS`-term
(`init = -c`) is `-c` times the IPA's final folded generator — the deployed flattening is the recursive
generator fold. -/
theorem commitGen_sFun_foldAll (u : List F) (init : F) (g : Fin (2 ^ u.length) → G) :
    commitGen g (sFun u init) = init • foldAll u g 0 := by
  induction u with
  | nil => simp [sFun, foldAll, commitGen]
  | cons uⱼ rest ih => rw [sFun_fold, ih, foldAll]

/-- The deployed `g`-scalars are `[-c] G'₀` (faithful to halo2 `Guard::use_challenges` + `compute_g`).
halo2 sets `G'₀ = ⟨compute_s(u, 1), g⟩` (`compute_g`) and `use_challenges` adds `compute_s(u, -c)` to the
`g`-scalars; here `eval_assembleFinalMsm`'s `computeS u (-c)` term equals `(-c) •` the folded generator
`foldAll u g 0` (which is `G'₀ = ⟨compute_s(u,1), g⟩`). So the §1 assembly's generator term is the
verifier's `[-c] G'₀`. -/
theorem computeS_gterm_foldAll (u : List F) (c : F) (g : Fin (2 ^ u.length) → G) :
    (∑ i, (computeS u (-c)).getD i.val 0 • g i) = (-c) • foldAll u g 0 := by
  rw [gterm_eq, commitGen_sFun_foldAll]

/-- The deployed `computeS` `g`-term from a `Fin m`-indexed challenge family is `[-c]·G'₀` — the
`List.ofFn`-length↔`m` transport of `computeS_gterm_foldAll`. The assembly indexes its round challenges as
`ch.ipaRound : Fin shape.k → Fp` and feeds `List.ofFn ch.ipaRound` to `computeS`; this reconciles that list's
length with `m = shape.k` (`List.length_ofFn`) via `Fin.cast`, so the `computeS` generator term of
`eval_assembleFinalMsm` is `[-c]` times the folded generator `foldAll = G'₀`. -/
theorem deployed_gterm_foldAll {m : ℕ} (f : Fin m → F) (c : F) (g : Fin (2 ^ m) → G) :
    (∑ i : Fin (2 ^ m), ((computeS (List.ofFn f) (-c)).getD i.val 0) • g i)
      = (-c) • foldAll (List.ofFn f) (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0 := by
  rw [← computeS_gterm_foldAll (List.ofFn f) c
    (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j))]
  apply Fintype.sum_equiv (finCongr (congrArg (2 ^ ·) (List.length_ofFn (f := f)).symm))
  intro i
  simp only [finCongr_apply, Fin.val_cast, Fin.cast_cast, Fin.cast_eq_self]

end Zcash.Snark
