import Mathlib.Data.Real.StarOrdered
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.MatrixStorage

/-!
# Dual storage inequality from the controllability Stein inequality

This is the row-contraction step in the balanced-truncation error proof.
Both weighted norms and their inverse matrices are actual finite matrices.
-/
namespace Populus.ModelReduction.Certified
open Matrix
noncomputable section
variable {n m : ℕ}

theorem inverse_weighted_row_contraction (P : Mat n n) (D : Mat m m)
    (T : Mat n m) (hP : P.PosDef) (hD : D.PosDef)
    (h : (P-T*D*T.transpose).PosSemidef) :
    (D⁻¹-T.transpose*P⁻¹*T).PosSemidef := by
  letI := hP.isUnit.invertible
  letI := hD.isUnit.invertible
  letI := hD.inv.isUnit.invertible
  have hb : (Matrix.fromBlocks P T T.conjTranspose D⁻¹).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₂₂ P T hD.inv).2
    simpa only [Matrix.inv_inv_of_invertible,Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hr := (Matrix.PosDef.fromBlocks₁₁ T D⁻¹ hP).1 hb
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hr

theorem inverse_weighted_row_storage (P : Mat n n) (D : Mat m m)
    (T : Mat n m) (hP : P.PosDef) (hD : D.PosDef)
    (h : (P-T*D*T.transpose).PosSemidef) (v : Rn m) :
    storage P⁻¹ (act T v) ≤ storage D⁻¹ v := by
  have hr := (inverse_weighted_row_contraction P D T hP hD h).dotProduct_mulVec_nonneg
    (v : Fin m → ℝ)
  have hT (y : Fin n → ℝ) : dotProduct v (T.transpose *ᵥ y)=dotProduct (T *ᵥ v) y := by
    rw [dotProduct_mulVec,Matrix.vecMul_transpose]
  simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,
    ← Matrix.mulVec_mulVec,hT] at hr
  change _ ≤ _
  simpa only [storage,act,Matrix.toLpLin_apply] using (sub_nonneg.mp hr)

end
end Populus.ModelReduction.Certified
