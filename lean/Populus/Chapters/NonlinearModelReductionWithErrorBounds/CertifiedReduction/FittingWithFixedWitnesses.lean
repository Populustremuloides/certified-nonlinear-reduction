import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.NeuralTrajectoryFitting
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ConstructedCertificate
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.PlantTransfer

/-!
# Actual prediction-loss convergence under fixed finite matrix witnesses

This proves the joint fitting and certification construction once the fixed
witnesses exist. The strict bounded-real converse needed to obtain those
witnesses from Assumption 1 is a remaining obligation, not a hidden premise
claimed to have been proved by this supporting theorem.
-/
namespace Populus.ModelReduction.Certified
open scoped Topology ENNReal BigOperators
open Filter
noncomputable section
variable {n q r m p p_u p_z N H : ℕ}

/-- The paper's averaged full autoregressive physical-state prediction loss.
`Fin H` indexes times 1 through H, not initialization at time zero. -/
def L_pred (M : NominalMatrices q m p p_u p_z) (C_x : Mat n q)
    (F : Rn n → Rn m → Rn n) (x₀ : Fin N → Rn n) (u : Fin N → ℕ → Rn m)
    (θ : NeuralParameter n q m p_u p_z) (H : ℕ) : ℝ :=
  ((N : ℝ)*(H : ℝ))⁻¹ * ∑ i : Fin N, ∑ k : Fin H,
    ‖act C_x (rollout (neuralUpdate M θ.a θ.c) (Φ_θ C_x θ.ψ (x₀ i)) (u i) (k+1))-
      rollout F (x₀ i) (u i) (k+1)‖^2

/-- Actual finite neural full-model prediction loss converges to zero against
an exactly represented physical plant on any finite training dataset. -/
theorem finite_neural_prediction_loss_tendsto_zero [NeZero N] [NeZero H]
    (M : NominalMatrices q m p p_u p_z) (C_x : Mat n q)
    (F : Rn n → Rn m → Rn n) (Φ : Rn n → Rn q) (hΦ : Continuous Φ)
    (hreconstruct : ∀ x, act C_x (Φ x)=x) (hΦ0 : Φ 0=0)
    (Δ_z_star : Rn q → Rn p_z) (Δ_u_star : Rn q → Rn m → Rn p_u)
    (hcz : Continuous Δ_z_star) (hcu : Continuous (fun v : Rn q×Rn m => Δ_u_star v.1 v.2))
    (hz : ∀ z, ‖Δ_z_star z‖≤‖z‖) (hu : ∀ z u, ‖Δ_u_star z u‖≤‖u‖)
    (hidentity : ∀ x u, M.fullUpdate Δ_z_star Δ_u_star (Φ x) u=Φ (F x u))
    (x₀ : Fin N → Rn n) (u : Fin N → ℕ → Rn m) :
    ∃ θ : ℕ → NeuralParameter n q m p_u p_z,
      (∀ ℓ x, act C_x (Φ_θ C_x (θ ℓ).ψ x)=x) ∧
      (∀ ℓ, Φ_θ C_x (θ ℓ).ψ 0=0) ∧
      Tendsto (fun ℓ => L_pred M C_x F x₀ u (θ ℓ) H) atTop (nhds 0) := by
  obtain ⟨θ,hθC,hθ0,htraj⟩ := finite_neural_training_trajectories_converge (H:=H)
    M C_x Φ hΦ hreconstruct hΦ0 Δ_z_star Δ_u_star hcz hcu hz hu x₀ u
  refine ⟨θ,hθC,hθ0,?_⟩
  have hterm (i : Fin N) (k : Fin H) :
      Tendsto (fun ℓ => ‖act C_x (rollout (neuralUpdate M (θ ℓ).a (θ ℓ).c)
        (Φ_θ C_x (θ ℓ).ψ (x₀ i)) (u i) (k+1))-rollout F (x₀ i) (u i) (k+1)‖^2)
        atTop (nhds 0) := by
    have hstate := htraj i (k+1) (by have := k.isLt; omega)
    have hphysical := (Matrix.toEuclideanLin C_x).continuous_of_finiteDimensional.continuousAt.tendsto.comp hstate
    have heq : act C_x (rollout (M.fullUpdate Δ_z_star Δ_u_star) (Φ (x₀ i)) (u i) (k+1))=
        rollout F (x₀ i) (u i) (k+1) := by
      rw [exact_lifted_trajectory F (M.fullUpdate Δ_z_star Δ_u_star) Φ hidentity,hreconstruct]
    simp only [act] at heq
    rw [heq] at hphysical
    have hz' := (tendsto_iff_norm_sub_tendsto_zero.1 hphysical).pow 2
    simpa only [Function.comp_apply,sub_self,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow] using hz'
  have hs := tendsto_finset_sum Finset.univ (fun i _ =>
    tendsto_finset_sum Finset.univ (fun k _ => hterm i k))
  have hconst : Tendsto (fun _ : ℕ => ((N : ℝ)*(H : ℝ))⁻¹) atTop
      (nhds (((N : ℝ)*(H : ℝ))⁻¹)) := tendsto_const_nhds
  have hscaled := hconst.mul hs
  simpa only [L_pred,Finset.sum_const_zero,mul_zero] using hscaled

/-- Joint fitting/certification for actual neural predictors, with the finite
matrix witnesses held fixed. This is the full constructive portion of the
main theorem after witness existence has been established. -/
theorem fit_and_certify_with_fixed_witnesses [NeZero q] [NeZero r] [NeZero N] [NeZero H]
    (M : NominalMatrices q m p p_u p_z) (C_x : Mat n q)
    (F : Rn n → Rn m → Rn n) (Φ : Rn n → Rn q) (hΦ : Continuous Φ)
    (hreconstruct : ∀ x, act C_x (Φ x)=x) (hΦ0 : Φ 0=0)
    (Δ_z_star : Rn q → Rn p_z) (Δ_u_star : Rn q → Rn m → Rn p_u)
    (hcz : Continuous Δ_z_star) (hcu : Continuous (fun v : Rn q×Rn m => Δ_u_star v.1 v.2))
    (hz : ∀ z, ‖Δ_z_star z‖≤‖z‖) (hu : ∀ z u, ‖Δ_u_star z u‖≤‖u‖)
    (hidentity : ∀ x u, M.fullUpdate Δ_z_star Δ_u_star (Φ x) u=Φ (F x u))
    (W_r : Mat r q) (V_r : Mat q r) (R : ReductionWitnesses q r)
    (hfinite : R.B_r M W_r V_r≠⊤)
    (x₀ : Fin N → Rn n) (u : Fin N → ℕ → Rn m) :
    ∃ θ : ℕ → NeuralParameter n q m p_u p_z,
      Tendsto (fun ℓ => L_pred M C_x F x₀ u (θ ℓ) H) atTop (nhds 0) ∧
      (∀ ℓ x, act C_x (Φ_θ C_x (θ ℓ).ψ x)=x) ∧
      (∀ ℓ, Φ_θ C_x (θ ℓ).ψ 0=0) ∧
      (∀ ℓ, ReductionGuarantees
        (nonlinearResponse M (1 : Mat q q) (Δ_z (θ ℓ).a) (Δ_u (θ ℓ).c))
        (nonlinearResponse (M.reduced W_r V_r) V_r (Δ_z (θ ℓ).a) (Δ_u (θ ℓ).c))
        (fun z => drivenUpdate M (1 : Mat q q) (Δ_z (θ ℓ).a) (Δ_u (θ ℓ).c) z 0)
        (fun z => drivenUpdate (M.reduced W_r V_r) V_r (Δ_z (θ ℓ).a) (Δ_u (θ ℓ).c) z 0)
        (R.B_r M W_r V_r)) := by
  obtain ⟨θ,hθC,hθ0,hloss⟩ := finite_neural_prediction_loss_tendsto_zero (H:=H) M C_x F Φ hΦ
    hreconstruct hΦ0 Δ_z_star Δ_u_star hcz hcu hz hu hidentity x₀ u
  refine ⟨θ,hloss,hθC,hθ0,fun ℓ => ?_⟩
  exact certified_nonlinear_state_reduction M W_r V_r R hfinite
    (Δ_z (θ ℓ).a) (Δ_z (θ ℓ).a) (Δ_u (θ ℓ).c) (Δ_u (θ ℓ).c)
    (norm_Δ_z_le (θ ℓ).a) (norm_Δ_u_le (θ ℓ).c)
    (norm_Δ_z_le (θ ℓ).a) (norm_Δ_u_le (θ ℓ).c)

end
end Populus.ModelReduction.Certified
