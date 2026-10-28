import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ReductionComparison

/-!
# Transfer to a plant with an exact lifted reference representation

Paper: `cor:plant`, Appendix H. The global lifted identity, physical
reconstruction and origin-preserving initialization are explicit hypotheses.
The conclusion is not a claim that finite fitting data prove those hypotheses.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {n q r m p p_u p_z : ℕ}

def plantResponse (F : Rn n → Rn m → Rn n) (S_y : Mat p n)
    (u : ℕ → Rn m) (k : ℕ) : Rn p := act S_y (rollout F 0 u k)

/-- Exact representation propagates along every trajectory and every input,
not merely through a fixed finite training dataset. -/
theorem exact_lifted_trajectory
    (F : Rn n → Rn m → Rn n) (F_tilde : Rn q → Rn m → Rn q)
    (Φ : Rn n → Rn q)
    (hidentity : ∀ x u, F_tilde (Φ x) u=Φ (F x u))
    (x₀ : Rn n) (u : ℕ → Rn m) (k : ℕ) :
    rollout F_tilde (Φ x₀) u k=Φ (rollout F x₀ u k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change F_tilde (rollout F_tilde (Φ x₀) u k) (u k)=Φ (F (rollout F x₀ u k) (u k))
    rw [ih,hidentity]

/-- The plant and its exact lifted reference have identical physical outputs. -/
theorem plantResponse_eq_exact_reference
    (F : Rn n → Rn m → Rn n) (S_y : Mat p n) (C_x : Mat n q)
    (Φ : Rn n → Rn q) (hΦ0 : Φ 0=0) (hreconstruct : ∀ x, act C_x (Φ x)=x)
    (N : NominalMatrices q m p p_u p_z) (hC : N.C=S_y*C_x)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hidentity : ∀ x u, drivenUpdate N (1 : Mat q q) Δ_z Δ_u (Φ x) u=Φ (F x u)) :
    plantResponse F S_y=nonlinearResponse N (1 : Mat q q) Δ_z Δ_u := by
  funext u k
  have ht := exact_lifted_trajectory F (drivenUpdate N (1 : Mat q q) Δ_z Δ_u) Φ hidentity 0 u k
  rw [hΦ0] at ht
  simp only [plantResponse,nonlinearResponse,ht,hC,act_mul,hreconstruct]

/-- **Paper Corollary `cor:plant`: Transfer to an exactly represented plant.**

A reference and neural approximant may have different residuals. Shared
nominal matrices, certified gain uppers and global envelopes give the same
bound against the plant, because the reference representation is exact.
-/
theorem transfer_to_exactly_represented_plant [NeZero q] [NeZero r]
    (F : Rn n → Rn m → Rn n) (S_y : Mat p n) (C_x : Mat n q)
    (Φ : Rn n → Rn q) (hΦ0 : Φ 0=0) (hreconstruct : ∀ x, act C_x (Φ x)=x)
    (N : NominalMatrices q m p p_u p_z) (hC : N.C=S_y*C_x)
    (W_r : Mat r q) (V_r : Mat q r) (hV : Function.Injective (act V_r))
    (hA : Schur N.A) (hA_hat : Schur (N.reduced W_r V_r).A)
    (G G_hat : GainBounds)
    (hG : G.Valid N (1 : Mat q q)) (hG_hat : G_hat.Valid (N.reduced W_r V_r) V_r)
    («b_r⁰» : ℝ) (hb : 0≤«b_r⁰»)
    (hnominal : inducedGain (fun u k => nominalResponse N u k-
      nominalResponse (N.reduced W_r V_r) u k) ≤ ENNReal.ofReal «b_r⁰»)
    (Δ_z_ref Δ_z_θ : Rn q → Rn p_z) (Δ_u_ref Δ_u_θ : Rn q → Rn m → Rn p_u)
    (hz_ref : ∀ z, ‖Δ_z_ref z‖ ≤ ‖z‖) (hu_ref : ∀ z u, ‖Δ_u_ref z u‖ ≤ ‖u‖)
    (hz_θ : ∀ z, ‖Δ_z_θ z‖ ≤ ‖z‖) (hu_θ : ∀ z u, ‖Δ_u_θ z u‖ ≤ ‖u‖)
    (hidentity : ∀ x u, drivenUpdate N (1 : Mat q q) Δ_z_ref Δ_u_ref (Φ x) u=Φ (F x u)) :
    inducedGain (fun u k => plantResponse F S_y u k-
      nonlinearResponse (N.reduced W_r V_r) V_r Δ_z_θ Δ_u_θ u k) ≤
        ENNReal.ofReal (G.ε+«b_r⁰»+G_hat.ε) := by
  rw [plantResponse_eq_exact_reference F S_y C_x Φ hΦ0 hreconstruct N hC Δ_z_ref Δ_u_ref hidentity]
  exact (uniform_nonlinear_comparison N W_r V_r hV hA hA_hat G G_hat hG hG_hat
    «b_r⁰» hb hnominal Δ_z_ref Δ_z_θ Δ_u_ref Δ_u_θ hz_ref hu_ref hz_θ hu_θ).2.2.2.2.2.2

end
end Populus.ModelReduction.Certified
