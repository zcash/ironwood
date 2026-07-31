import Zcash.Snark.Soundness.Deployed.Verification

/-!
# Closed-form IPA assembly algebra

The flat verifier equation folds one IPA round at a time. `roundSum_cons`, `computeB_cons`, and
`CF_cons` expose the commitment, generator, value, and blinding updates used by the straight-line
AGM proof. `deployedVerifierEq_cf` identifies this algebra with halo2's deployed verifier equation.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The sum `Σⱼ ([uⱼ⁻¹]Lⱼ + [uⱼ]Rⱼ)` contributed by the IPA rounds. -/
def roundSum (rounds : List (G × G)) (u : List F) : G :=
  ((rounds.zip u).map (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum

@[simp] theorem roundSum_nil_rounds (u : List F) : roundSum ([] : List (G × G)) u = 0 := by
  simp [roundSum]

@[simp] theorem roundSum_nil_challenges (rounds : List (G × G)) : roundSum rounds ([] : List F) = 0 := by
  simp [roundSum, List.zip_nil_right]

/-- Split the first round's contribution from `roundSum`. -/
theorem roundSum_cons (L R : G) (rounds : List (G × G)) (u₀ : F) (u : List F) :
    roundSum ((L, R) :: rounds) (u₀ :: u) = (u₀⁻¹ • L + u₀ • R) + roundSum rounds u := by
  simp [roundSum]

/-! ## The `computeB` round recursion (the `b`-value fold) -/

/-- The second `computeB` accumulator after `|u|` rounds is `x ^ (2 ^ |u|)`. -/
theorem computeB_pt {F : Type*} [CommRing F] (x : F) (u : List F) :
    (u.reverse.foldl (fun acc uⱼ => (acc.1 * (1 + uⱼ * acc.2), acc.2 * acc.2)) ((1 : F), x)).2
      = x ^ (2 ^ u.length) := by
  induction u with
  | nil => simp
  | cons u₀ tail ih =>
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      List.length_cons, ← pow_add, pow_succ, Nat.mul_two]

/-- Split the leading challenge's factor from `computeB`. -/
theorem computeB_cons {F : Type*} [CommRing F] (x u₀ : F) (tail : List F) :
    computeB x (u₀ :: tail) = computeB x tail * (1 + u₀ * x ^ (2 ^ tail.length)) := by
  rw [computeB, computeB, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
    ← computeB_pt x tail]

/-! ## The commitment/generator side of the closed-form equation folds per round

`gPart` contains the adjusted commitment, round sum, and folded generator. -/

/-- The adjusted commitment, IPA round sum, and final folded-generator term. -/
def gPart (rounds : List (G × G)) (u : List F) (g : Fin (2 ^ u.length) → G) (P' : G) (c : F) : G :=
  P' + roundSum rounds u + (-c) • foldAll u g 0

/-- Fold the first round point into the commitment and generators. -/
theorem gPart_cons (L R : G) (rounds : List (G × G)) (u₀ : F) (u : List F)
    (g : Fin (2 ^ (u₀ :: u).length) → G) (P' : G) (c : F) :
    gPart ((L, R) :: rounds) (u₀ :: u) g P' c
      = gPart rounds u (foldGens g u₀⁻¹) (P' + u₀⁻¹ • L + u₀ • R) c := by
  simp only [gPart, roundSum_cons, foldAll]
  abel

/-! ## The eval-vector fold telescopes to `computeB`

The recursive verifier folds `b = (1, x, x², …)` to one value. The lemmas below show that this value
is the flat verifier's `computeB x u`.
-/

/-- One eval-vector fold produces a shorter eval vector and one scalar factor. -/
theorem foldGens_evalVector {F : Type*} [Field F] (k : ℕ) (x u : F) :
    foldGens (evalVector (k + 1) x) u = (1 + u⁻¹ * x ^ (2 ^ k)) • evalVector k x := by
  funext i
  simp only [foldGens, Pi.add_apply, Pi.smul_apply, loHalf, hiHalf, evalVector, smul_eq_mul]
  rw [pow_add]
  ring

/-- `foldGens` commutes with scalar multiplication. -/
theorem foldGens_smul {F : Type*} [Field F] {k : ℕ} (c : F) (b : Fin (2 ^ (k + 1)) → F) (v : F) :
    foldGens (c • b) v = c • foldGens b v := by
  funext i
  simp only [foldGens, Pi.add_apply, Pi.smul_apply, loHalf, hiHalf, smul_eq_mul]
  ring

/-- `foldAll` commutes with scalar multiplication. -/
theorem foldAll_smul {F : Type*} [Field F] (c : F) (u : List F) (b : Fin (2 ^ u.length) → F) :
    foldAll (G := F) u (c • b) = c • foldAll (G := F) u b := by
  induction u with
  | nil => rfl
  | cons u₀ rest ih => rw [foldAll, foldGens_smul, ih, foldAll]

/-- Folding the eval vector through all challenges gives `computeB x u`. -/
theorem foldAll_evalVector {F : Type*} [Field F] (x : F) (u : List F) :
    foldAll (G := F) u (evalVector u.length x) (0 : Fin (2 ^ 0)) = computeB x u := by
  induction u with
  | nil => simp [foldAll, evalVector, computeB]
  | cons u₀ rest ih =>
    rw [foldAll]
    simp only [List.length_cons]
    rw [foldGens_evalVector, inv_inv, foldAll_smul, Pi.smul_apply, ih, smul_eq_mul, computeB_cons]
    ring

/-! ## The closed-form verifier equation folds one round (the keystone)

`CF` is the flat verifier equation with abstract `U` and `W` coefficients. `CF_cons` shows that a
round point represented over `(g, U, W)` folds the commitment, value, and blinding exactly as the
deployed tree does.
-/

/-- The flat verifier equation with abstract coefficients for `U` and `W`. -/
def CF (rounds : List (G × G)) (u : List F) (g : Fin (2 ^ u.length) → G) (P : G) (c : F)
    (Uc : F) (U : G) (Wc : F) (W : G) : G :=
  gPart rounds u g P c + Uc • U + Wc • W

/-- Fold one represented round point through the flat verifier equation. -/
theorem CF_cons (Lg Rg U W : G) (Lv Lw Rv Rw : F) (rounds : List (G × G)) (u₀ : F) (u : List F)
    (g : Fin (2 ^ (u₀ :: u).length) → G) (P : G) (c Uc Wc : F) :
    CF ((Lg + Lv • U + Lw • W, Rg + Rv • U + Rw • W) :: rounds) (u₀ :: u) g P c Uc U Wc W
      = CF rounds u (foldGens g u₀⁻¹) (P + u₀⁻¹ • Lg + u₀ • Rg) c
          (Uc + u₀⁻¹ * Lv + u₀ * Rv) U (Wc + u₀⁻¹ * Lw + u₀ * Rw) W := by
  simp only [CF]
  rw [gPart_cons]
  simp only [gPart]
  module

/-! ## The adjusted-commitment connection: halo2's verifier equation is the closed form
-/

/-- Halo2's deployed IPA verifier equation is the closed form `CF = 0`. -/
theorem deployedVerifierEq_cf {shape : Shape} [DecidableEq F] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G)
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) :
    DeployedIpaVerifierEq g w u vk instanceCommitment ps ch ↔
      CF (List.ofFn ps.ipaRounds) (List.ofFn ch.ipaRound)
          (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j))
          (multiopenCommitment g w u vk instanceCommitment ps ch
            + (∑ i, ([-(multiopenValue vk instanceCommitment ps ch)].getD i.val 0) • g i) + ch.xi • ps.ipaS)
          ps.ipaC (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) u (-ps.ipaF) w = 0 := by
  unfold DeployedIpaVerifierEq CF gPart roundSum multiopenCommitment multiopenValue
  constructor <;> intro h <;> linear_combination (norm := abel) h

end Zcash.Snark
