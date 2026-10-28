import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.NormalizationDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Sharp smooth-normalization estimates used in the written density proof

The actual Euclidean derivative and global nonexpansiveness are proved here,
independently of the alternative compact-open density proof already checked.
-/
namespace Populus.ModelReduction.Certified
open scoped InnerProductSpace NNReal
noncomputable section
variable {p : ℕ}
set_option maxHeartbeats 800000

def νDerivative (x : Rn p) : Rn p →L[ℝ] Rn p :=
  (Real.sqrt (1+‖x‖^2))⁻¹ • ContinuousLinearMap.id ℝ (Rn p)-
    ((Real.sqrt (1+‖x‖^2))^3)⁻¹ • (innerSL ℝ x).smulRight x

theorem ν_hasFDerivAt (x : Rn p) : HasFDerivAt ν (νDerivative x) x := by
  have hs : 0<Real.sqrt (1+‖x‖^2) := by positivity
  have hsq := (hasFDerivAt_id (𝕜:=ℝ) x).norm_sq
  have hroot := (hsq.const_add 1).sqrt (by positivity : 1+‖x‖^2≠0)
  have hinv := (hasDerivAt_inv (ne_of_gt hs)).comp_hasFDerivAt x hroot
  have hi : HasFDerivAt (fun v : Rn p => (Real.sqrt (1+‖v‖^2))⁻¹)
      (-((Real.sqrt (1+‖x‖^2))^3)⁻¹ • innerSL ℝ x) x := by
    apply hinv.congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul,id_eq]
    field_simp [ne_of_gt hs]
    ring
  have h := hi.smul (hasFDerivAt_id (𝕜:=ℝ) x)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [νDerivative,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,
    neg_smul,smul_neg,sub_eq_add_neg,smul_smul,ContinuousLinearMap.neg_apply,id_eq]
  rfl

/-- The exact Jacobian is contractive in the Euclidean norm. -/
theorem νDerivative_apply_norm_le (x v : Rn p) : ‖νDerivative x v‖≤‖v‖ := by
  let a : ℝ := Real.sqrt (1+‖x‖^2)
  let s : ℝ := ⟪x,v⟫_ℝ
  have ha : 0<a := by dsimp [a]; positivity
  have ha2 : a^2=1+‖x‖^2 := Real.sq_sqrt (by positivity)
  have ha1 : 1≤a := by nlinarith [sq_nonneg ‖x‖]
  have heq : ‖νDerivative x v‖^2=‖v‖^2/a^2-(‖x‖^2+2)*s^2/a^6 := by
    change ‖a⁻¹ • v-(a^3)⁻¹ • (s • x)‖^2=_
    rw [norm_sub_sq_real]
    simp only [norm_smul,Real.norm_eq_abs,real_inner_smul_left,real_inner_smul_right,
      real_inner_comm x v,mul_pow,sq_abs]
    change (a⁻¹)^2*‖v‖^2-2*((a^3)⁻¹*(s*(a⁻¹*s)))+
      ((a^3)⁻¹)^2*(s^2*‖x‖^2)=_
    field_simp [ne_of_gt ha]
    nlinarith [ha2]
  have hsub : 0≤(‖x‖^2+2)*s^2/a^6 := by positivity
  have hdiv : ‖v‖^2/a^2≤‖v‖^2 := by
    apply div_le_self (sq_nonneg _)
    nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [heq]
  linarith

theorem νDerivative_norm_le_one (x : Rn p) : ‖νDerivative x‖≤1 := by
  apply (νDerivative x).opNorm_le_bound (by norm_num)
  intro v
  simpa only [one_mul] using νDerivative_apply_norm_le x v

/-- Smooth unit-ball normalization is globally nonexpansive, with constant 1. -/
theorem ν_lipschitz : LipschitzWith 1 (ν : Rn p → Rn p) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (ν_hasFDerivAt x).differentiableAt)
  intro x
  rw [(ν_hasFDerivAt x).fderiv]
  exact_mod_cast νDerivative_norm_le_one x

theorem norm_ν_sub_le (x y : Rn p) : ‖ν x-ν y‖≤‖x-y‖ := by
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using (ν_lipschitz (p:=p)).dist_le_mul x y

end
end Populus.ModelReduction.Certified
