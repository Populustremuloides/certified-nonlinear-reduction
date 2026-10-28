import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.VectorBlocks
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.WeightedRowContraction

/-!
# The cancellation behind a single balanced-truncation step

The discarded block has one common Hankel singular value τ. The retained
weights need not coincide. This cancellation is the reason the nominal
error estimate involves twice the discarded singular value.
-/
namespace Populus.ModelReduction.Certified
open scoped BigOperators InnerProductSpace
noncomputable section
variable {a b : ℕ}

def balancedEnergy (σ : Fin a → ℝ) (τ : ℝ) (z : Rn (a+b)) : ℝ :=
  (∑ i,σ i*(take z i)^2)+τ*‖drop z‖^2

theorem balanced_tail_cancellation (σ : Fin a → ℝ) (τ : ℝ) (hτ : τ≠0)
    (x y : Rn (a+b)) (v : Rn b)
    (hv : drop y-drop x=(2:ℝ) • v) :
    balancedEnergy σ τ (x+join (0 : Rn a) v)+
        τ^2*balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ (y-join (0 : Rn a) v)=
      balancedEnergy σ τ x+τ^2*balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ y-
        2*τ*‖v‖^2 := by
  have ht₁ : take (x+join (0 : Rn a) v)=take x := by ext i; simp [take,join]
  have ht₂ : take (y-join (0 : Rn a) v)=take y := by ext i; simp [take,join]
  have hd₁ : drop (x+join (0 : Rn a) v)=drop x+v := by ext i; simp [drop,join]
  have hd₂ : drop (y-join (0 : Rn a) v)=drop y-v := by ext i; simp [drop,join]
  have hi : ⟪drop y,v⟫_ℝ-⟪drop x,v⟫_ℝ=2*‖v‖^2 := by
    have hh := congrArg (fun t : Rn b => ⟪t,v⟫_ℝ) hv
    simpa only [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq] using hh
  simp only [balancedEnergy,ht₁,ht₂,hd₁,hd₂,norm_add_sq_real,norm_sub_sq_real]
  have he : τ^2*τ⁻¹=τ := by field_simp
  simp only [mul_add,← mul_assoc,he]
  nlinarith [congrArg (fun t : ℝ => τ*t) hi]

end
end Populus.ModelReduction.Certified
