import Zcash.Snark.ZeroKnowledge.DigestFiber
import Zcash.Common.Probability.DistributionKernel

/-!
# Recovering raw oracle digests without additional statistical loss

Sample a wide-reduced challenge, then a uniform raw digest from its exact
preimage fiber. The joint law is exactly that of a uniform digest and its
reduction, even when the continuation depends on both values.
-/

namespace Zcash.Snark.ZeroKnowledge

open Zcash.Arithmetic (Fp)
open Zcash.Common
open scoped ENNReal

/-- Recovering a raw digest from its wide-reduced field value preserves every joint continuation. -/
theorem fieldSample_digest_recovery_law {A : Type*}
    (next : Fp → Fin challengeDigestCard → PMF A) :
    fieldSample.bind (fun field => (digestFiberSample field).bind (next field)) =
      (PMF.uniformOfFintype (Fin challengeDigestCard)).bind
        (fun digest => next (digest.val : Fp) digest) := by
  classical
  apply PMF.ext
  intro value
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left, ← mul_assoc, fieldSample_mul_digestFiberSample]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro digest
  rw [tsum_eq_single (digest.val : Fp)]
  · simp only [if_true, PMF.uniformOfFintype_apply, Fintype.card_fin]
  · intro field hne
    simp only [if_neg (Ne.symm hne), zero_mul]

/-- The simulator's recovered digest always has the field value which it must answer. -/
theorem digestFiberSample_support (field : Fp) (digest : Fin challengeDigestCard) :
    digest ∈ (digestFiberSample field).support ↔ (digest.val : Fp) = field := by
  rw [PMF.mem_support_iff, digestFiberSample_apply]
  by_cases h : (digest.val : Fp) = field
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)⟩
  · rw [if_neg h]
    exact ⟨fun hn => (hn rfl).elim, fun he => (h he).elim⟩

end Zcash.Snark.ZeroKnowledge
