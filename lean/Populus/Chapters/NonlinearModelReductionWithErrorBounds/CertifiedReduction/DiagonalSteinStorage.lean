import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.BalancedOneStep

/-! Actual diagonal Stein inequalities imply the two balanced storage bounds. -/
namespace Populus.ModelReduction.Certified
open Matrix
open scoped BigOperators
noncomputable section
variable {d m p : ℕ}

def diagonalEnergy (ρ : Fin d → ℝ) (z : Rn d) : ℝ := ∑ i,ρ i*(z i)^2

theorem storage_diagonal (ρ : Fin d → ℝ) (z : Rn d) :
    storage (Matrix.diagonal ρ) z=diagonalEnergy ρ z := by
  simp only [storage,dotProduct,diagonalEnergy]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_diagonal]
  ring

def rowJoin (A : Mat d d) (B : Mat d m) : Mat d (d+m) :=
  fun i => Fin.addCases (A i) (B i)

theorem rowJoin_act (A : Mat d d) (B : Mat d m) (z : Rn d) (u : Rn m) :
    act (rowJoin A B) (join z u)=act A z+act B u := by
  ext i
  simp [act,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,rowJoin,join,Fin.sum_univ_add]

theorem rowJoin_diagonal_product (ρ : Fin d → ℝ) (A : Mat d d) (B : Mat d m) :
    rowJoin A B*Matrix.diagonal (Fin.addCases ρ (fun _ : Fin m => (1:ℝ)))*
        (rowJoin A B).transpose=
      A*Matrix.diagonal ρ*A.transpose+B*B.transpose := by
  have he : rowJoin A B*Matrix.diagonal (Fin.addCases ρ (fun _ : Fin m => (1:ℝ)))=
      rowJoin (A*Matrix.diagonal ρ) B := by
    ext i j
    rw [Matrix.mul_diagonal]
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
      simp [rowJoin,Matrix.mul_diagonal]
  rw [he]
  ext i j
  simp [Matrix.mul_apply,Matrix.transpose_apply,rowJoin,Fin.sum_univ_add]

theorem diagonalEnergy_join (ρ : Fin d → ℝ) (z : Rn d) (u : Rn m) :
    diagonalEnergy (Fin.addCases ρ (fun _ : Fin m => (1:ℝ))) (join z u)=
      diagonalEnergy ρ z+‖u‖^2 := by
  simp [diagonalEnergy,join,Fin.sum_univ_add,EuclideanSpace.real_norm_sq_eq]


theorem diagonal_inverse_of_positive (ρ : Fin d → ℝ) (hρ : ∀ i,0<ρ i) :
    (Matrix.diagonal ρ)⁻¹=Matrix.diagonal (fun i => (ρ i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  have he : (fun i => (ρ i)⁻¹*ρ i)=(fun _ => (1:ℝ)) := by
    funext i
    exact inv_mul_cancel₀ (ne_of_gt (hρ i))
  rw [he,Matrix.diagonal_one]

theorem controllability_stein_storage (ρ : Fin d → ℝ) (hρ : ∀ i,0<ρ i)
    (A : Mat d d) (B : Mat d m)
    (h : (Matrix.diagonal ρ-A*Matrix.diagonal ρ*A.transpose-B*B.transpose).PosSemidef)
    (z : Rn d) (u : Rn m) :
    diagonalEnergy (fun i => (ρ i)⁻¹) (act A z+act B u)≤
      diagonalEnergy (fun i => (ρ i)⁻¹) z+‖u‖^2 := by
  have hp : (Matrix.diagonal ρ).PosDef := Matrix.PosDef.diagonal hρ
  have hψ : ∀ i : Fin (d+m),(0:ℝ)<Fin.addCases ρ (fun _ : Fin m => (1:ℝ)) i := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hρ j
    · simp
  have hd := Matrix.PosDef.diagonal hψ
  have hi := inverse_weighted_row_storage (Matrix.diagonal ρ)
    (Matrix.diagonal (Fin.addCases ρ (fun _ : Fin m => (1:ℝ))))
    (rowJoin A B) hp hd
    (by rw [rowJoin_diagonal_product]; simpa [sub_add_eq_sub_sub] using h) (join z u)
  rw [rowJoin_act,diagonal_inverse_of_positive ρ hρ,
    diagonal_inverse_of_positive _ hψ,
    storage_diagonal,storage_diagonal] at hi
  have he : (fun i => (Fin.addCases ρ (fun _ : Fin m => (1:ℝ)) i)⁻¹)=
      Fin.addCases (fun i => (ρ i)⁻¹) (fun _ : Fin m => (1:ℝ)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  rw [he,diagonalEnergy_join] at hi
  exact hi

theorem storage_congruence (X : Mat d d) (A : Mat d m) (z : Rn m) :
    storage (A.transpose*X*A) z=storage X (act A z) := by
  simp only [storage,← Matrix.mulVec_mulVec]
  rw [dotProduct_mulVec,Matrix.vecMul_transpose]
  rfl

theorem storage_gram (C : Mat p d) (z : Rn d) :
    storage (C.transpose*C) z=‖act C z‖^2 := by
  have he : C.transpose*C=C.transpose*(1 : Mat p p)*C := by simp
  rw [he,storage_congruence,← Matrix.diagonal_one,storage_diagonal]
  simp [diagonalEnergy,EuclideanSpace.real_norm_sq_eq]

theorem observability_stein_storage (ρ : Fin d → ℝ)
    (A : Mat d d) (C : Mat p d)
    (h : (Matrix.diagonal ρ-A.transpose*Matrix.diagonal ρ*A-C.transpose*C).PosSemidef)
    (z : Rn d) :
    diagonalEnergy ρ (act A z)+‖act C z‖^2≤diagonalEnergy ρ z := by
  have hh := h.dotProduct_mulVec_nonneg (z : Fin d → ℝ)
  change 0≤storage (Matrix.diagonal ρ-A.transpose*Matrix.diagonal ρ*A-C.transpose*C) z at hh
  have hs (X Y : Mat d d) : storage (X-Y) z=storage X z-storage Y z := by
    simp [storage,Matrix.sub_mulVec,dotProduct_sub]
  rw [hs,hs,storage_diagonal,storage_congruence,storage_diagonal,storage_gram] at hh
  linarith

end
end Populus.ModelReduction.Certified
