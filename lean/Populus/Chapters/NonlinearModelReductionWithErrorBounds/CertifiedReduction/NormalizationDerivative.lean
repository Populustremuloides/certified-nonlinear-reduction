import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.AnchoredReluModel
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace Populus.ModelReduction.Certified
noncomputable section
variable {p d n m k : ℕ}

@[simp] theorem matCLM_mul (A : Mat n m) (B : Mat m k) : (matCLM A).comp (matCLM B)=matCLM (A*B) := by
  apply ContinuousLinearMap.ext
  intro x
  exact (act_mul A B x).symm

@[simp] theorem matCLM_smul (t : ℝ) (A : Mat n m) : matCLM (t • A)=t • matCLM A := by
  ext x i
  simp [matCLM,act,Matrix.toEuclideanLin,Matrix.smul_mulVec]

def takeLinear : Rn (p+d) →ₗ[ℝ] Rn p where
  toFun := take
  map_add' x y := by ext i; rfl
  map_smul' t x := by ext i; rfl

def takeCLM : Rn (p+d) →L[ℝ] Rn p := takeLinear.mkContinuous 1
  (fun x => by simpa only [one_mul] using norm_take_le x)
@[simp] theorem takeCLM_apply (x : Rn (p+d)) : takeCLM x=take x := rfl

/-- At zero the smooth unit-ball normalization has exactly the identity
Jacobian, as used in the frozen-model nonincremental proof. -/
theorem ν_hasFDerivAt_zero : HasFDerivAt (ν : Rn p → Rn p) (ContinuousLinearMap.id ℝ (Rn p)) 0 := by
  let η : Rn p → ℝ := fun z => (Real.sqrt (1+‖z‖^2))⁻¹
  have hn : DifferentiableAt ℝ (fun z : Rn p => ‖z‖^2) 0 := differentiableAt_id.norm_sq ℝ
  have hs : DifferentiableAt ℝ (fun z : Rn p => Real.sqrt (1+‖z‖^2)) 0 :=
    (hn.const_add 1).sqrt (by norm_num)
  have hi : DifferentiableAt ℝ η 0 := hs.inv (by norm_num)
  have h := hi.hasFDerivAt.smul (hasFDerivAt_id (𝕜:=ℝ) (0 : Rn p))
  simpa [η,ν] using h

end
end Populus.ModelReduction.Certified
