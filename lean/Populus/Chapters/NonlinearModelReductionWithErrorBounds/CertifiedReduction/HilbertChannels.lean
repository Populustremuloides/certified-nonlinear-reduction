import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.LpSignals
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.LinearResponseAlgebra
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.OperatorGains

/-!
# Actual nominal channels as bounded Hilbert-space linear operators

No gain premise changes: the same prefix/induced bound proved earlier gives
output membership, linearity follows from the recurrence, and the operator
norm is bounded by the same scalar. This supplies the analytic operators for
the strict bounded-real existence proof, not an assumed storage witness.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {d b o : ℕ}

theorem channel_l2_membership (A : Mat d d) (B : Mat d b) (O : Mat o d)
    (g : ℝ) (h : HasPrefixChannelGain A B O g) (u : L2 (Rn b)) :
    FiniteEnergy (fun k => act O (linearResponse A B (fun j => u j) k)) :=
  finiteEnergy_of_gain_bound _ (fun k => u k) (L2.finiteEnergy u) g
    (ℓ₂_le_of_prefix_bound _ _ g h.1 (h.2 _))

def channelLinear (A : Mat d d) (B : Mat d b) (O : Mat o d)
    (g : ℝ) (h : HasPrefixChannelGain A B O g) : L2 (Rn b) →ₗ[ℝ] L2 (Rn o) where
  toFun u := toL2 (fun k => act O (linearResponse A B (fun j => u j) k)) (channel_l2_membership A B O g h u)
  map_add' u v := by
    apply lp.ext
    funext k
    simp only [toL2_apply,lp.coeFn_add,Pi.add_apply,linearResponse_add,act_add]
  map_smul' t u := by
    apply lp.ext
    funext k
    simp only [toL2_apply,lp.coeFn_smul,Pi.smul_apply,linearResponse_smul,act_smul,RingHom.id_apply]

theorem channelLinear_norm_bound (A : Mat d d) (B : Mat d b) (O : Mat o d)
    (g : ℝ) (h : HasPrefixChannelGain A B O g) (u : L2 (Rn b)) :
    ‖channelLinear A B O g h u‖≤g*‖u‖ := by
  have hp := ℓ₂_le_of_prefix_bound (fun k => act O (linearResponse A B (fun j => u j) k))
    (fun k => u k) g h.1 (h.2 _)
  have hy : ℓ₂ (fun k => act O (linearResponse A B (fun j => u j) k))=
      ENNReal.ofReal ‖channelLinear A B O g h u‖ := L2.ℓ₂_eq_norm (channelLinear A B O g h u)
  rw [hy,L2.ℓ₂_eq_norm,← ENNReal.ofReal_mul h.1] at hp
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg h.1 (norm_nonneg u))).1 hp

def channelOperator (A : Mat d d) (B : Mat d b) (O : Mat o d)
    (g : ℝ) (h : HasPrefixChannelGain A B O g) : L2 (Rn b) →L[ℝ] L2 (Rn o) :=
  (channelLinear A B O g h).mkContinuous g (channelLinear_norm_bound A B O g h)

@[simp] theorem channelOperator_apply (A : Mat d d) (B : Mat d b) (O : Mat o d)
    (g : ℝ) (h : HasPrefixChannelGain A B O g) (u : L2 (Rn b)) (k : ℕ) :
    channelOperator A B O g h u k=act O (linearResponse A B (fun j => u j) k) := rfl

theorem norm_channelOperator_le (A : Mat d d) (B : Mat d b) (O : Mat o d)
    (g : ℝ) (h : HasPrefixChannelGain A B O g) : ‖channelOperator A B O g h‖≤g :=
  ContinuousLinearMap.opNorm_le_bound _ h.1 (channelLinear_norm_bound A B O g h)

end
end Populus.ModelReduction.Certified
