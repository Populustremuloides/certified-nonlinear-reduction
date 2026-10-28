import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.EnvelopeApproximation

/-!
# Sharp nonexpansiveness of radial projection

This checks the sharper norm inequality used in the appendix proof, beyond
the factor-two estimate already sufficient for its named density conclusion.
-/
namespace Populus.ModelReduction.Certified
open scoped InnerProductSpace
noncomputable section
variable {p : ℕ}

/-- The radial clamp is the Euclidean projection onto the closed unit ball,
expressed by its variational inequality. -/
theorem rad_variational (a w : Rn p) (hw : ‖w‖≤1) : ⟪a-rad a, w-rad a⟫_ℝ≤0 := by
  by_cases ha : ‖a‖≤1
  · have heq : rad a=a := by simp [rad,Populus.PaperEvidence.ModelReduction.rad,max_eq_left ha]
    simp [heq]
  · have har : 1≤‖a‖ := (le_of_not_ge ha)
    have hap : 0<‖a‖ := by linarith
    have hunit : ‖rad a‖=1 := by
      simp only [rad,Populus.PaperEvidence.ModelReduction.rad,max_eq_right har,norm_smul,
        Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hap)]
      exact inv_mul_cancel₀ (ne_of_gt hap)
    have hscale : ‖a‖ • rad a=a := by
      simp only [rad,Populus.PaperEvidence.ModelReduction.rad,max_eq_right har,smul_smul,
        mul_inv_cancel₀ (ne_of_gt hap),one_smul]
    have hsub : a-rad a=(‖a‖-1) • rad a := by
      calc
        _ = ‖a‖ • rad a-rad a := by rw [hscale]
        _ = _ := by module
    have hi : ⟪rad a,w⟫_ℝ≤1 := (real_inner_le_norm _ _).trans (by rw [hunit]; simpa using hw)
    rw [hsub,real_inner_smul_left,inner_sub_right,real_inner_self_eq_norm_sq,hunit]
    nlinarith

/-- Exact nonexpansiveness of the normalization in the written proof. -/
theorem norm_rad_sub_le_sharp (a b : Rn p) : ‖rad a-rad b‖≤‖a-b‖ := by
  have h₁ := rad_variational a (rad b) (Populus.PaperEvidence.ModelReduction.norm_rad_le_one b)
  have h₂ := rad_variational b (rad a) (Populus.PaperEvidence.ModelReduction.norm_rad_le_one a)
  have hmonotone : ‖rad a-rad b‖^2≤⟪a-b,rad a-rad b⟫_ℝ := by
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq] at h₁ h₂ ⊢
    rw [norm_sub_sq_real]
    have hsym : ⟪rad b,rad a⟫_ℝ=⟪rad a,rad b⟫_ℝ := real_inner_comm _ _
    linarith
  have hc := real_inner_le_norm (a-b) (rad a-rad b)
  by_cases hzero : ‖rad a-rad b‖=0
  · rw [hzero]; exact norm_nonneg _
  · have hp : 0<‖rad a-rad b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

end
end Populus.ModelReduction.Certified
