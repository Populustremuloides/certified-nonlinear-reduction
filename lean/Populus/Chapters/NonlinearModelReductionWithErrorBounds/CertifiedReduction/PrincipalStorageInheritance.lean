import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.PrincipalSchur

/-! The two diagonal storage inequalities survive principal truncation. -/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {a b m p : ℕ}

theorem principal_observability_storage (σ : Fin a → ℝ) (τ : ℝ) (hτ : 0≤τ)
    (A : Mat (a+b) (a+b)) (C : Mat p (a+b))
    (h : ∀ z,balancedEnergy σ τ (act A z)+‖act C z‖^2≤balancedEnergy σ τ z)
    (z : Rn a) :
    diagonalEnergy σ (act (principalA A) z)+‖act (principalC C) z‖^2≤diagonalEnergy σ z := by
  have hi := h (join z (0 : Rn b))
  have he : balancedEnergy σ τ (join z (0 : Rn b))=diagonalEnergy σ z := by
    simp [balancedEnergy,diagonalEnergy]
  rw [he,← act_principalC C] at hi
  have hhead : balancedEnergy σ τ (act A (join z (0 : Rn b)))=
      diagonalEnergy σ (act (principalA A) z)+τ*‖drop (act A (join z (0 : Rn b)))‖^2 := by
    rw [act_principalA]
    rfl
  rw [hhead] at hi
  linarith [mul_nonneg hτ (sq_nonneg ‖drop (act A (join z (0 : Rn b)))‖)]

theorem principal_controllability_storage (σ : Fin a → ℝ) (τ : ℝ) (hτ : 0≤τ)
    (A : Mat (a+b) (a+b)) (B : Mat (a+b) m)
    (h : ∀ z u,balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ (act A z+act B u)≤
      balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ z+‖u‖^2)
    (z : Rn a) (u : Rn m) :
    diagonalEnergy (fun i => (σ i)⁻¹) (act (principalA A) z+act (principalB B) u)≤
      diagonalEnergy (fun i => (σ i)⁻¹) z+‖u‖^2 := by
  have hi := h (join z (0 : Rn b)) u
  have he : balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ (join z (0 : Rn b))=
      diagonalEnergy (fun i => (σ i)⁻¹) z := by simp [balancedEnergy,diagonalEnergy]
  rw [he] at hi
  have ht : take (act A (join z (0 : Rn b))+act B u)=
      act (principalA A) z+act (principalB B) u := by
    rw [act_principalA,act_principalB]
    ext i
    rfl
  have hhead : balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹
      (act A (join z (0 : Rn b))+act B u)=
      diagonalEnergy (fun i => (σ i)⁻¹) (act (principalA A) z+act (principalB B) u)+
        τ⁻¹*‖drop (act A (join z (0 : Rn b))+act B u)‖^2 := by
    rw [← ht]
    rfl
  rw [hhead] at hi
  linarith [mul_nonneg (inv_nonneg.2 hτ) (sq_nonneg ‖drop (act A (join z (0 : Rn b))+act B u)‖)]

end
end Populus.ModelReduction.Certified
