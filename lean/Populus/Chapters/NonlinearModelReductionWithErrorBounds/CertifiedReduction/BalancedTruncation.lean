import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.AppliedInputRestriction

/-!
# Paper Section 3.4: balancing, Schur stability and the nominal Hankel tail bound

Residual ports enter the controllability Gramian as independent nominal inputs.
The conclusion is a gain bound from the original applied-input port. The
projection is exactly W = Π T, V = R Πᵀ, with R = T⁻¹. No nominal error-gain
oracle is assumed. Positivity and the stated balancing identities suffice for
this proof; hence it also covers the paper's ordered, strictly separated cut.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {q m n : ℕ}

theorem firstInputMatrix_transformed (T : Mat q q) (B : Mat q m) (D : Mat q n) :
    firstInputMatrix (T*inputJoin B D)=T*B := by
  ext i j
  simp [firstInputMatrix,Matrix.mul_apply,inputJoin]

theorem stein_residual_posSemidef (X Y Z : Mat q q) (h : X=Y+Z) :
    (X-Y-Z).PosSemidef := by
  have he : X-Y-Z=0 := by rw [h]; abel
  rw [he]
  exact Matrix.PosSemidef.zero

/-- **Paper `def:balanced` and `eq:balanced-nominal-upper`.** -/
theorem balanced_truncation_specialization {r k m n p : ℕ}
    (σ : Fin (r+k) → ℝ) (hσ : ∀ i,0<σ i)
    (A : Mat (r+k) (r+k)) (B_u : Mat (r+k) m) (B_res : Mat (r+k) n)
    (C : Mat p (r+k)) (P Q T R : Mat (r+k) (r+k))
    (hA : Schur A) (hTR : T*R=1) (hRT : R*T=1)
    (hP : P=A*P*A.transpose+inputJoin B_u B_res*(inputJoin B_u B_res).transpose)
    (hQ : Q=A.transpose*Q*A+C.transpose*C)
    (hbalancedP : Matrix.diagonal σ=T*P*T.transpose)
    (hbalancedQ : Matrix.diagonal σ=R.transpose*Q*R) :
    balancedW T (Nat.le_add_right r k)*balancedV R (Nat.le_add_right r k)=1 ∧
      Schur (balancedW T (Nat.le_add_right r k)*A*balancedV R (Nat.le_add_right r k)) ∧
      inducedGain (fun u j => nominalOutput A B_u C u j-
        nominalOutput
          (balancedW T (Nat.le_add_right r k)*A*balancedV R (Nat.le_add_right r k))
          (balancedW T (Nat.le_add_right r k)*B_u)
          (C*balancedV R (Nat.le_add_right r k)) u j)≤ENNReal.ofReal (2*tailSum σ) := by
  have hp := balanced_controllability_stein A P T R (Matrix.diagonal σ) (inputJoin B_u B_res)
    hRT hP hbalancedP
  have hq := balanced_observability_stein A Q T R (Matrix.diagonal σ) C hRT hQ hbalancedQ
  have ho := observability_stein_storage σ (T*A*R) (C*R) (stein_residual_posSemidef _ _ _ hq)
  have hc := controllability_stein_storage σ hσ (T*A*R) (T*inputJoin B_u B_res)
    (stein_residual_posSemidef _ _ _ hp)
  have ha := balanced_retained_schur σ hσ (T*A*R) (T*inputJoin B_u B_res) (C*R)
    (schur_similarity A T R hTR hRT hA) ho hc
  have hb := balanced_tail_applied_input (m:=m) (n:=n) σ hσ
    (T*A*R) (T*inputJoin B_u B_res) (C*R) ho hc
  rw [firstInputMatrix_transformed] at hb
  refine ⟨balancedW_mul_balancedV T R _ hTR,?_,?_⟩
  · simpa only [balanced_projected_A] using ha
  · simp only [balanced_projected_A,balanced_projected_B,balanced_projected_C]
    simpa only [similarity_nominalOutput A B_u C T R hRT] using hb

end
end Populus.ModelReduction.Certified
