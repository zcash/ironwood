import Zcash.Snark.ZeroKnowledge.DigestLift
import Zcash.Snark.ZeroKnowledge.RandomTapeSource

/-!
# Exact recovery of a complete raw challenge tape

The independent per-field preimage samplers recover the entire joint digest
tape. Lifting a verifier view through this common kernel preserves its original
two-sided statistical error; it does not charge another wide-reduction hybrid.
-/

namespace Zcash.Snark.ZeroKnowledge

set_option exponentiation.threshold 1024
set_option maxRecDepth 8192

open Zcash.Arithmetic (Fp)
open Zcash.Common
open Zcash.Common.Probability
open scoped ENNReal

/-- Recover each raw challenge digest independently, conditional on its field value. -/
noncomputable def digestTapeFiberSample : {count : ℕ} → (Fin count → Fp) → PMF (Fin count → Fin challengeDigestCard)
  | 0, _ => PMF.pure Fin.elim0
  | _ + 1, fields => (digestFiberSample (fields 0)).bind fun digest =>
      (digestTapeFiberSample (Fin.tail fields)).map (Fin.cons digest)

/-- Independent field sampling followed by conditional digest recovery is exactly uniform raw sampling. -/
theorem digestTape_recovery_law {A : Type*} (count : ℕ) :
    ∀ next : (Fin count → Fp) → (Fin count → Fin challengeDigestCard) → PMF A,
      (independentTapeLaw fieldSample count).bind
          (fun fields => (digestTapeFiberSample fields).bind (next fields)) =
        (independentTapeLaw (PMF.uniformOfFintype (Fin challengeDigestCard)) count).bind
          (fun digests => next (fun i => ((digests i).val : Fp)) digests) := by
  induction count with
  | zero =>
    intro next
    simp only [independentTapeLaw, PMF.pure_bind, digestTapeFiberSample]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ count ih =>
    intro next
    calc
      _ = fieldSample.bind (fun field => (digestFiberSample field).bind fun digest =>
          (independentTapeLaw fieldSample count).bind fun fields =>
            (digestTapeFiberSample fields).bind fun digests =>
              next (Fin.cons field fields) (Fin.cons digest digests)) := by
        simp only [independentTapeLaw, PMF.bind_bind, PMF.bind_map, Function.comp_def,
          digestTapeFiberSample, Fin.cons_zero, Fin.tail_cons]
        congr 1
        funext field
        exact PMF.bind_comm _ _ _
      _ = fieldSample.bind (fun field => (digestFiberSample field).bind fun digest =>
          (independentTapeLaw (PMF.uniformOfFintype (Fin challengeDigestCard)) count).bind fun digests =>
            next (Fin.cons field (fun i => ((digests i).val : Fp))) (Fin.cons digest digests)) := by
        congr 1
        funext field
        congr 1
        funext digest
        exact ih _
      _ = (PMF.uniformOfFintype (Fin challengeDigestCard)).bind (fun digest =>
          (independentTapeLaw (PMF.uniformOfFintype (Fin challengeDigestCard)) count).bind fun digests =>
            next (Fin.cons (digest.val : Fp) (fun i => ((digests i).val : Fp)))
              (Fin.cons digest digests)) := fieldSample_digest_recovery_law _
      _ = _ := by
        simp only [independentTapeLaw, PMF.bind_bind, PMF.bind_map, Function.comp_def]
        congr 1
        funext digest
        congr 1
        funext digests
        congr 1
        funext i
        exact Fin.cases rfl (fun _ => rfl) i

/-- Attach a correctly distributed raw digest tape to an existing verifier view. -/
noncomputable def liftDigestTapeView {V : Type*} {count : ℕ}
    (fields : V → Fin count → Fp) (law : PMF V) : PMF ((Fin count → Fin challengeDigestCard) × V) :=
  law.bind fun view => (digestTapeFiberSample (fields view)).map (fun digests => (digests, view))

/-- The raw digest view preserves the same simulation error in both directions. -/
theorem liftDigestTapeView_error_bound {V : Type*} {count : ℕ}
    (fields : V → Fin count → Fp) {actual ideal : PMF V} {ε : ℝ≥0∞}
    (forward : PMFEventBiasLE actual ideal ε) (reverse : PMFEventBiasLE ideal actual ε) :
    PMFEventBiasLE (liftDigestTapeView fields actual) (liftDigestTapeView fields ideal) ε ∧
      PMFEventBiasLE (liftDigestTapeView fields ideal) (liftDigestTapeView fields actual) ε :=
  ⟨eventBias_bind_kernel forward _, eventBias_bind_kernel reverse _⟩

end Zcash.Snark.ZeroKnowledge
