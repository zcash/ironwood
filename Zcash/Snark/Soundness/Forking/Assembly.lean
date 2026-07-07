import Zcash.Snark.Soundness.Deployed.Verification
import Zcash.Snark.Soundness.Deployed.IpaPeel

/-!
# Structural special-soundness assembly (eliminating the monolithic `FiatShamirTree`)

`FiatShamirTree` currently assumes, in one opaque step, that an accepting deployed verifier equation yields a
`DeployedIpaTreeV` with `DeployedIpaAcceptV`. That bundles (i) the random-oracle / rewinding *forking* — a
cryptographic assumption that genuinely cannot be discharged in Lean — with (ii) a purely **structural**
bridge from accepting transcripts to the recursive ternary IPA tree, which is a proof-engineering problem,
not handwaving. This module builds (ii), so the residual shrinks to (i) alone.

## Roadmap (the structural bridge, built on the existing fold foundations)

The flat verifier equation `DeployedIpaVerifierEq` is `(closed form) = 0`, where the closed form
(`deployed_verification_eq`) is `P' + roundSum + [-c·b·z]U + [-f]W + [-c]·G'₀` with `P' = multiopen − [v]g₀ +
[ξ]S` the adjusted commitment. The recursive `DeployedIpaAcceptV` folds `P` by `(L,R,u)` per round down to a
leaf check. Bridging them:

1. **round-sum recursion** (`roundSum_cons`) — `roundSum` peels one `([uⱼ⁻¹]Lⱼ + [uⱼ]Rⱼ)` term per round.
2. **generator/value fold recursion** — `foldAll`, `foldGens`, `computeS_cons` already give the `g`/`b`
   one-round fold (`Soundness.Deployed.Fold`, `Soundness.Ipa.Soundness`).
3. **`computeB` one-round recursion** (`computeB_cons`) — the `b`-value fold (the `[-c·b·z]U` coefficient).
4. **one-round closed-form fold** (`CF_cons`) — combine 1–3: with the round point in its `(g,U,W)`
   representation, the closed form at challenge `u₀` equals the closed form of the folded instance
   `(foldGens g u₀⁻¹, P + u₀⁻¹Lg + u₀Rg, …)` over the remaining rounds, the value/blinding coefficients
   folding additively. The eval-vector fold telescopes to `computeB` (`foldAll_evalVector`, the value bridge).
5. **leaf reconciliation** (`CF_leaf_to_acceptV`) — at depth 0 (single generator) the closed form `= 0` gives
   the `DeployedIpaAcceptV` leaf, with the folded commitment in its `(g,U,W)` representation and the value
   carried on `U` via `z` (the form `deployed_leaf_peel` then peels, sound for `z ≠ 0`).
6. **ternary assembly** — three transcripts diverging at distinct nonzero `u` (the forking output) give a
   `DeployedIpaTreeV` node via Vandermonde (`vandermonde3`, `ipa_round_commit_sound`), recursed to the tree.

Steps 1–5 are proven below: the closed-form verifier equation folds round by round into the recursive tree
structure and reconciles to the `DeployedIpaAcceptV` leaf. Step 6's special-soundness *extraction* is now
likewise proven on the live flat path — `Soundness.Forking.Extractor.produceDeployed` /
`deployed_forking_tree` recover the round points' `(g,U,W)` representation by Vandermonde from
decomposition-free `DeployedForkValid` certificates; the *posited* node decomposition survives only on the
legacy `ForkAccept`/`FiatShamirForking` route (`Soundness.Main`). What stays the irreducible residual is
the random-oracle rewinding that *produces* the forked transcripts (with its query loss) — the honest
floor; the structural fold this module proves is the part downstream of having the transcripts.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The IPA rounds' contribution to the verifier equation: `Σⱼ ([uⱼ⁻¹] Lⱼ + [uⱼ] Rⱼ)`, pairing each prover
round `(Lⱼ, Rⱼ)` with its challenge `uⱼ`. This is the `roundSum` term of `deployed_verification_eq`'s closed
form, named so the per-round fold (step 4 of the roadmap) can peel it. -/
def roundSum (rounds : List (G × G)) (u : List F) : G :=
  ((rounds.zip u).map (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum

@[simp] theorem roundSum_nil_rounds (u : List F) : roundSum ([] : List (G × G)) u = 0 := by
  simp [roundSum]

@[simp] theorem roundSum_nil_challenges (rounds : List (G × G)) : roundSum rounds ([] : List F) = 0 := by
  simp [roundSum, List.zip_nil_right]

/-- One round peels off the head of the round-sum: `roundSum ((L,R) :: rounds) (u₀ :: u) = ([u₀⁻¹]L + [u₀]R)
+ roundSum rounds u`. The keystone of the per-round closed-form fold — the head term folds into the
commitment, the tail is the folded instance's round-sum. -/
theorem roundSum_cons (L R : G) (rounds : List (G × G)) (u₀ : F) (u : List F) :
    roundSum ((L, R) :: rounds) (u₀ :: u) = (u₀⁻¹ • L + u₀ • R) + roundSum rounds u := by
  simp [roundSum]

/-! ## Step 3 — the `computeB` round recursion (the `b`-value fold) -/

/-- The `computeB` fold's running point after `|u|` rounds is `x ^ (2 ^ |u|)` (it squares each round). The
auxiliary tracking the second fold component, needed to peel `computeB`'s leading round. -/
theorem computeB_pt {F : Type*} [CommRing F] (x : F) (u : List F) :
    (u.reverse.foldl (fun acc uⱼ => (acc.1 * (1 + uⱼ * acc.2), acc.2 * acc.2)) ((1 : F), x)).2
      = x ^ (2 ^ u.length) := by
  induction u with
  | nil => simp
  | cons u₀ tail ih =>
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      List.length_cons, ← pow_add, pow_succ, Nat.mul_two]

/-- One round of `computeB`: the leading challenge `u₀` contributes the factor `1 + u₀ · x ^ (2 ^ |tail|)` to
the product over the remaining challenges. The `b`-value fold underlying the deployed IPA's `[-c·b·z]U`
coefficient, peeled in step with the generators and the round-sum. -/
theorem computeB_cons {F : Type*} [CommRing F] (x u₀ : F) (tail : List F) :
    computeB x (u₀ :: tail) = computeB x tail * (1 + u₀ * x ^ (2 ^ tail.length)) := by
  rw [computeB, computeB, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
    ← computeB_pt x tail]

/-! ## Step 4a — the commitment/generator side of the closed-form equation folds per round

The closed-form verifier equation (`deployed_verification_eq`) is `gPart + [-c·b·z]·U + [-f]·W`, where the
`gPart` collects the adjusted commitment, the round-sum, and the folded generator. The `U`/`W` terms do not
fold per round (the `computeB` value is global, `computeB_cons`); the `gPart` does, and that fold is the
commitment/generator recursion the deployed tree (`DeployedIpaAcceptV`) runs on. -/

/-- The commitment/generator side of the deployed verifier equation: the adjusted commitment `P'`, plus the
round-sum, plus `[-c]` times the folded generator `foldAll`. (The `U`/`W`/value terms are handled separately
at the leaf.) -/
def gPart (rounds : List (G × G)) (u : List F) (g : Fin (2 ^ u.length) → G) (P' : G) (c : F) : G :=
  P' + roundSum rounds u + (-c) • foldAll u g 0

/-- One round of the commitment/generator fold: the leading round `(L₀, R₀)` folds into the commitment
(`P' ↦ P' + [u₀⁻¹]L₀ + [u₀]R₀`) and the generators by `foldGens g u₀⁻¹`, leaving the remaining-rounds
`gPart`. This is exactly the deployed tree's per-node commitment/generator fold. -/
theorem gPart_cons (L R : G) (rounds : List (G × G)) (u₀ : F) (u : List F)
    (g : Fin (2 ^ (u₀ :: u).length) → G) (P' : G) (c : F) :
    gPart ((L, R) :: rounds) (u₀ :: u) g P' c
      = gPart rounds u (foldGens g u₀⁻¹) (P' + u₀⁻¹ • L + u₀ • R) c := by
  simp only [gPart, roundSum_cons, foldAll]
  abel

/-! ## Step 4b — the eval-vector fold telescopes to `computeB`

The deployed tree (`DeployedIpaAcceptV`) folds the eval vector `b = (1, x, x², …)` by `foldGens b uᵢ` per
round and reads the single leaf value `b₀`. The flat verifier equation's `U`-coefficient is the global
product `computeB`. Folding `evalVector` one round multiplies it by the scalar `1 + u⁻¹·x^(2^k)` and halves
its length, so folding through all rounds telescopes the leaf `b₀` to a `computeB`-shaped product — the
bridge between the recursive `b`-fold and the flat `computeB`. -/

/-- One round of the eval-vector fold: folding `evalVector (k+1) x` by `foldGens · u` scales it by the factor
`1 + u⁻¹·x^(2^k)` and drops to `evalVector k x`. (The same fold the generators undergo, on the value side.)
This is the per-round step whose product over all rounds is `computeB`. -/
theorem foldGens_evalVector {F : Type*} [Field F] (k : ℕ) (x u : F) :
    foldGens (evalVector (k + 1) x) u = (1 + u⁻¹ * x ^ (2 ^ k)) • evalVector k x := by
  funext i
  simp only [foldGens, Pi.add_apply, Pi.smul_apply, loHalf, hiHalf, evalVector, smul_eq_mul]
  rw [pow_add]
  ring

/-- `foldGens` is linear in the vector: folding a scaled vector scales the fold. The eval-vector fold picks
up a scalar factor each round (`foldGens_evalVector`), and this carries that factor out through the
remaining rounds. -/
theorem foldGens_smul {F : Type*} [Field F] {k : ℕ} (c : F) (b : Fin (2 ^ (k + 1)) → F) (v : F) :
    foldGens (c • b) v = c • foldGens b v := by
  funext i
  simp only [foldGens, Pi.add_apply, Pi.smul_apply, loHalf, hiHalf, smul_eq_mul]
  ring

/-- `foldAll` is linear in the vector (it is iterated `foldGens`): the per-round scalar factors the
eval-vector fold accumulates pull out to a single scalar on the fully-folded value. -/
theorem foldAll_smul {F : Type*} [Field F] (c : F) (u : List F) (b : Fin (2 ^ u.length) → F) :
    foldAll (G := F) u (c • b) = c • foldAll (G := F) u b := by
  induction u with
  | nil => rfl
  | cons u₀ rest ih => rw [foldAll, foldGens_smul, ih, foldAll]

/-- **The value bridge.** Folding the eval vector `b = (1, x, x², …)` through challenges `u` by `foldAll`
(the inverse-convention fold, `foldGens · uⱼ⁻¹`) telescopes its single leaf value to exactly the flat
`computeB x u`. This identifies the deployed tree's recursive `b`-fold (read at the leaf as `b₀`) with the
flat verifier equation's global `U`-coefficient, the keystone of the closed-form↔tree bridge. -/
theorem foldAll_evalVector {F : Type*} [Field F] (x : F) (u : List F) :
    foldAll (G := F) u (evalVector u.length x) (0 : Fin (2 ^ 0)) = computeB x u := by
  induction u with
  | nil => simp [foldAll, evalVector, computeB]
  | cons u₀ rest ih =>
    rw [foldAll]
    simp only [List.length_cons]
    rw [foldGens_evalVector, inv_inv, foldAll_smul, Pi.smul_apply, ih, smul_eq_mul, computeB_cons]
    ring

/-! ## Step 4 — the closed-form verifier equation folds one round (the keystone)

`CF` is the closed-form verifier equation's left-hand side, abstracted over the value/blinding coefficients:
`gPart` (the commitment/generator side) plus `[Uc]·U + [Wc]·W`. For the deployed equation the coefficients
are `Uc = -c·computeB·z` and `Wc = -f`.

The keystone `CF_cons` folds it one round, given the prover's round point `L`/`R` in their **`(g, U, W)`
representation** `L = Lg + [Lv]·U + [Lw]·W`, `R = Rg + [Rv]·U + [Rw]·W` (the decomposition the extractor
recovers from the forked transcripts). The commitment/generator side folds by `gPart_cons`; the value
coefficient `Uc` and blinding coefficient `Wc` fold **additively** — `Uc ↦ Uc + u₀⁻¹·Lv + u₀·Rv`,
`Wc ↦ Wc + u₀⁻¹·Lw + u₀·Rw` — because the `U`/`W` parts of `[u₀⁻¹]L + [u₀]R` peel out of the commitment slot.
This is exactly the deployed tree's per-node fold of `(P, v, blind)`, with `Uc` tracking `z·v` and `Wc`
tracking the blinding. The structural fold is unconditional; the cryptographic content (which `Lv`/`Rv`/… the
prover is committed to) lives in the extractor that supplies the representation. -/

/-- The closed-form verifier equation's left-hand side, abstracted over the value/blinding coefficients:
the commitment/generator side `gPart` plus `[Uc]·U + [Wc]·W`. The deployed equation is `CF … = 0` with
`Uc = -c·computeB·z`, `Wc = -f`. -/
def CF (rounds : List (G × G)) (u : List F) (g : Fin (2 ^ u.length) → G) (P : G) (c : F)
    (Uc : F) (U : G) (Wc : F) (W : G) : G :=
  gPart rounds u g P c + Uc • U + Wc • W

/-- **The closed-form one-round fold.** Given the leading round point in its `(g, U, W)` representation
`L = Lg + [Lv]U + [Lw]W`, `R = Rg + [Rv]U + [Rw]W`, one round of the closed-form equation folds to the
remaining-rounds closed form of the folded instance: the generators fold by `foldGens g u₀⁻¹`, the
commitment by its `g`-part `P + [u₀⁻¹]Lg + [u₀]Rg`, and the value/blinding coefficients fold additively
(`Uc ↦ Uc + u₀⁻¹·Lv + u₀·Rv`, `Wc ↦ Wc + u₀⁻¹·Lw + u₀·Rw`). The deployed tree's per-node fold of `P`, `v`,
`blind` in one identity. -/
theorem CF_cons (Lg Rg U W : G) (Lv Lw Rv Rw : F) (rounds : List (G × G)) (u₀ : F) (u : List F)
    (g : Fin (2 ^ (u₀ :: u).length) → G) (P : G) (c Uc Wc : F) :
    CF ((Lg + Lv • U + Lw • W, Rg + Rv • U + Rw • W) :: rounds) (u₀ :: u) g P c Uc U Wc W
      = CF rounds u (foldGens g u₀⁻¹) (P + u₀⁻¹ • Lg + u₀ • Rg) c
          (Uc + u₀⁻¹ * Lv + u₀ * Rv) U (Wc + u₀⁻¹ * Lw + u₀ * Rw) W := by
  simp only [CF]
  rw [gPart_cons]
  simp only [gPart]
  module

/-! ## Step 5 — leaf reconciliation: the depth-0 closed form is the deployed tree's leaf check

At depth 0 the generators are a single point `g 0` and the closed form has folded all rounds. With the value
coefficient set to the deployed reference `Uc = -(z · b₀)` (where `b₀ = commitGen b (·↦c)` is the folded eval
value, `foldAll_evalVector`) and `Wc = -f`, and the folded commitment given in its `(g, U, W)` representation
`P = ⟨aP, g⟩ + [z·v]U + [blind]W`, the closed-form equation `CF [] [] g P c Uc U Wc W = 0` rearranges to
exactly halo2's reformulated leaf relation — the `DeployedIpaAcceptV` leaf. This is where `z ≠ 0` is needed
downstream (`deployed_leaf_peel`) to cancel the `U`-side; here the reconciliation is the pure rearrangement. -/

/-- **Leaf reconciliation.** The depth-0 closed-form equation, with the folded commitment in its `(g, U, W)`
representation `P = ⟨aP, g⟩ + [z·v]U + [blind]W` and value coefficient `-(z·b₀)`, is the deployed tree's
reformulated leaf check `DeployedIpaAcceptV g b U W z ⟨aP,g⟩ v blind (leaf c f)`: the closed form rearranges
to `⟨aP,g⟩ + [z·v]U + [blind]W = ⟨c,g⟩ + [z·c·b₀]U + [f]W`. -/
theorem CF_leaf_to_acceptV (g : Fin (2 ^ 0) → G) (b : Fin (2 ^ 0) → F) (U W : G) (z : F)
    (aP : Fin (2 ^ 0) → F) (v blind c f : F)
    (hCF : CF [] [] g (commitGen g aP + (z * v) • U + blind • W) c
              (-(z * commitGen b (fun _ => c))) U (-f) W = 0) :
    DeployedIpaAcceptV g b U W z (commitGen g aP) v blind (.leaf c f) := by
  refine ⟨aP, rfl, ?_⟩
  have hg : commitGen g (fun _ => c) = c • g 0 := by simp [commitGen]
  rw [hg, ← sub_eq_zero, ← hCF]
  simp only [CF, gPart, roundSum, foldAll, List.zip_nil_left, List.map_nil, List.sum_nil, add_zero]
  module

/-! ## Step 6 — the tree assembly: the forking output yields `DeployedIpaAcceptV`

`DeployedIpaTreeV` is a 3-ary special-soundness object, so it cannot come from a single accepting transcript:
the forking procedure supplies, at each IPA round, three accepting continuations with a shared prefix and
distinct nonzero challenges. `ForkAccept` packages exactly that forking output — the same recursion as
`DeployedIpaAcceptV` (the verifier's per-round fold of `g`, `b`, `P`, the value and the blinding) but with
the *flat closed-form equation* at each leaf (an accepting transcript) in place of the reformulated check.

`forkAccept_to_acceptV` is the deterministic assembly: it threads the recursion down to the leaves and
reconciles each via `CF_leaf_to_acceptV`, turning the forking output into `DeployedIpaAcceptV` — which
`deployed_to_acceptV` + `ipa_soundV` then extract a witness from. This discharges the tree-assembly content
of the Fiat-Shamir bridge: what stays is supplying `ForkAccept` itself (the rewinding that produces the
distinct-challenge transcripts and pins each round point's `(g,U,W)` representation), the random-oracle floor. -/

/-- The forking procedure's output, recursive over the special-soundness tree: the same per-round fold as
`DeployedIpaAcceptV`, but each leaf carries the *flat closed-form verifier equation* (`CF … = 0`, an
accepting transcript) with its commitment opening `aP`, rather than the reformulated leaf check. A node
records three accepting continuations at distinct nonzero challenges `u₁, u₂, u₃` (the 3-special-soundness
forking). -/
def ForkAccept : {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → G → G → F → G → F → F →
    DeployedIpaTreeV F G d → Prop
  | 0, g, b, U, W, z, P, v, blind, .leaf c f =>
      ∃ aP : Fin (2 ^ 0) → F, P = commitGen g aP ∧
        CF [] [] g (P + (z * v) • U + blind • W) c (-(z * commitGen b (fun _ => c))) U (-f) W = 0
  | _ + 1, g, b, U, W, z, P, v, blind, .node L R Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        ForkAccept (foldGens g u₁) (foldGens b u₁) U W z
          (P + u₁⁻¹ • L + u₁ • R) (v + u₁⁻¹ • Lv + u₁ • Rv) (blind + u₁⁻¹ • Lw + u₁ • Rw) t₁ ∧
        ForkAccept (foldGens g u₂) (foldGens b u₂) U W z
          (P + u₂⁻¹ • L + u₂ • R) (v + u₂⁻¹ • Lv + u₂ • Rv) (blind + u₂⁻¹ • Lw + u₂ • Rw) t₂ ∧
        ForkAccept (foldGens g u₃) (foldGens b u₃) U W z
          (P + u₃⁻¹ • L + u₃ • R) (v + u₃⁻¹ • Lv + u₃ • Rv) (blind + u₃⁻¹ • Lw + u₃ • Rw) t₃

/-- **The tree assembly.** The forking output `ForkAccept` yields the deployed accept predicate
`DeployedIpaAcceptV`. By induction on the tree: each node's per-round fold is identical, and each leaf's flat
closed-form equation is reconciled to the reformulated leaf check by `CF_leaf_to_acceptV`. This is the
deterministic, `sorry`/`axiom`-free discharge of the tree-assembly handwave — the forking *output* is the
input, and the recursive `DeployedIpaAcceptV` (hence, via `deployed_to_acceptV`/`ipa_soundV`, an opening) is
the proven consequence. -/
theorem forkAccept_to_acceptV {U W : G} {z : F} :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) → (v blind : F) →
      (t : DeployedIpaTreeV F G d) → ForkAccept g b U W z P v blind t →
      DeployedIpaAcceptV g b U W z P v blind t
  | 0, g, b, P, v, blind, .leaf c f, h => by
      obtain ⟨aP, hP, hCF⟩ := h
      rw [hP] at hCF ⊢
      exact CF_leaf_to_acceptV g b U W z aP v blind c f hCF
  | _ + 1, g, b, P, v, blind, .node L R Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, ha₁, ha₂, ha₃⟩ := h
      exact ⟨h12, h13, h23, hu₁, hu₂, hu₃,
        forkAccept_to_acceptV _ _ _ _ _ t₁ ha₁,
        forkAccept_to_acceptV _ _ _ _ _ t₂ ha₂,
        forkAccept_to_acceptV _ _ _ _ _ t₃ ha₃⟩

/-! ## The adjusted-commitment connection: halo2's verifier equation is the closed form

The forking development runs on the closed form `CF`. To tie it to halo2's actual deployed verifier equation
`DeployedIpaVerifierEq`, this step identifies the two: the verifier equation *is* `CF = 0` with the
**adjusted commitment** `P' = multiopen + [-v]g₀ + [ξ]S` (the value term `[-v]g₀` and the blinding poly `[ξ]S`
folded into the commitment slot), `Uc = -c·b·z`, `Wc = -f`, over the proof's round points and IPA challenges.
It is a pure reordering of the same seven group terms (`abel`). -/

/-- **halo2's verifier equation is the closed form.** `DeployedIpaVerifierEq` holds iff the closed-form
equation `CF = 0` does, with the adjusted commitment `P' = multiopen + [-v]g₀ + [ξ]S`, `Uc = -c·b·z`,
`Wc = -f`, on the proof's IPA rounds and challenges. The two are the same seven-term sum reordered — the
deterministic bridge putting the forking machinery (`CF_cons`, the value bridge, leaf reconciliation) onto
halo2's actual equation. -/
theorem deployedVerifierEq_cf {shape : Shape} [DecidableEq F] [DecidableEq G] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G)
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G) (ch : Challenges shape.k F) :
    DeployedIpaVerifierEq g w u vk ps ch ↔
      CF (List.ofFn ps.ipaRounds) (List.ofFn ch.ipaRound)
          (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j))
          (multiopenCommitment g w u vk ps ch
            + (∑ i, ([-(multiopenValue vk ps ch)].getD i.val 0) • g i) + ch.xi • ps.ipaS)
          ps.ipaC (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) u (-ps.ipaF) w = 0 := by
  unfold DeployedIpaVerifierEq CF gPart roundSum multiopenCommitment multiopenValue
  constructor <;> intro h <;> linear_combination (norm := abel) h

end Zcash.Snark
