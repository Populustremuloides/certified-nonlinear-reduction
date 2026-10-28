import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.NeuralFamily

/-!
# Accurate learning with certified stable reduction

Paper correspondence: `thm:main` and Appendix E. The universal family Θ is
fixed independently of the plant or dataset. Its finite neural parameters
include the chosen nominal matrices, physical decoder/readout, projection and
finite matrix witnesses. Reference feasibility supplies those witnesses by
the proved strict bounded-real theorem. Actual physical autoregressive loss
converges to zero; the same certificate remains finite at every capacity.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal Topology
open Filter
noncomputable section
variable {n q r m p N H : ℕ}

/-- **Paper Theorem `thm:main`: Accurate learning with certified stable reduction.**

Quantifiers follow the manuscript: one fixed finite neural family and one
certificate work for every feasible exactly represented physical update and
every finite training dataset. A finite parameter meets every positive fitting
tolerance, and a sequence drives the averaged physical-state loss to zero
under one unchanged finite certificate. The certificate predicate supplies
GAS, finite individual gains and the reduction-error bound (in fact GES).
No optimizer convergence, reduced-accuracy guarantee or physical identification
from finite data is assumed or asserted.
-/
theorem accurate_learning_with_certified_stable_reduction
    [NeZero q] [NeZero r] [NeZero N] [NeZero H] :
    ∃ 𝓑_r : Θ n q r m p → ℝ≥0∞, IsReductionCertificate 𝓑_r ∧
      ∀ (F : Rn n → Rn m → Rn n), F∈𝓕_q n q m → ReferenceFeasible F q r →
      ∀ (S_y : Mat p n) (x₀ : Fin N → Rn n) (u : Fin N → ℕ → Rn m),
      (∀ ε_fit : ℝ, 0<ε_fit → ∃ θ : Θ n q r m p,
        θ.S_y=S_y ∧ θ.𝓛_pred F x₀ u H≤ε_fit^2 ∧ 𝓑_r θ≠⊤) ∧
      (∃ θ : ℕ → Θ n q r m p,
        (∀ ℓ, (θ ℓ).S_y=S_y) ∧
        Tendsto (fun ℓ => (θ ℓ).𝓛_pred F x₀ u H) atTop (nhds 0) ∧
        (∀ ℓ, 𝓑_r (θ ℓ)=𝓑_r (θ 1)) ∧ 𝓑_r (θ 1)≠⊤) := by
  refine ⟨Θ.𝓑_r,neural_family_certificate,fun F hF hfeasible S_y x₀ u => ?_⟩
  obtain ⟨ρ,⟨P⟩⟩ := hfeasible
  obtain ⟨R,hR⟩ := ρ.matrix_witnesses P S_y
  let M := ρ.observedNominal S_y
  have hfinite : R.B_r M P.W_r P.V_r≠⊤ := (R.B_r_finite_iff M P.W_r P.V_r).2 hR
  obtain ⟨networks,hC,h0,hloss⟩ := finite_neural_prediction_loss_tendsto_zero (H:=H)
    M ρ.nominal.C F ρ.Φ ρ.continuous_Φ ρ.reconstruct ρ.Φ_zero
    ρ.Δ_z ρ.Δ_u ρ.continuous_Δ_z ρ.continuous_Δ_u ρ.envelope_z ρ.envelope_u ρ.identity x₀ u
  let θ : ℕ → Θ n q r m p := fun ℓ => {
    p_u := ρ.p_u
    p_z := ρ.p_z
    nominal := M
    C_x := ρ.nominal.C
    S_y := S_y
    output_identity := rfl
    reconstruction_inverse := C_x_mul_dagger ρ.nominal.C ρ.Φ ρ.reconstruct
    W_r := P.W_r
    V_r := P.V_r
    left_inverse := P.left_inverse
    networks := networks ℓ
    witnesses := R }
  have hθloss : Tendsto (fun ℓ => (θ ℓ).𝓛_pred F x₀ u H) atTop (nhds 0) := hloss
  have hθcert (ℓ : ℕ) : (θ ℓ).𝓑_r=R.B_r M P.W_r P.V_r := rfl
  refine ⟨?_,⟨θ,(fun ℓ => rfl),hθloss,fun ℓ => (hθcert ℓ).trans (hθcert 1).symm,?_⟩⟩
  · intro ε_fit hε
    have heventually := (tendsto_order.1 hθloss).2 (ε_fit^2) (sq_pos_of_pos hε)
    obtain ⟨ℓ,hℓ⟩ := heventually.exists
    exact ⟨θ ℓ,rfl,hℓ.le,by rwa [hθcert ℓ]⟩
  · rwa [hθcert 1]

end
end Populus.ModelReduction.Certified
