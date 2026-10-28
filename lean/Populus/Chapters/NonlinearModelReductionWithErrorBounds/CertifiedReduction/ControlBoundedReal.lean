import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ClearedBoundedReal

/-!
# Rational control-port BRL checks for the sqrt(2)-scaled saved injection

The saved control port is sqrt(2)[P_0 P_1]. A block-diagonal congruence
removes the irrational factor from the finite arithmetic certificate.
-/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {n b o : ℕ}

def boundedRealSquared (A : Mat n n) (B : Mat n b) (O : Mat o n) (X : Mat n n) (g2 : ℝ) :
    Matrix (Fin n ⊕ Fin b) (Fin n ⊕ Fin b) ℝ :=
  Matrix.fromBlocks (A.transpose*X*A-X+O.transpose*O)
    (A.transpose*X*B) (B.transpose*X*A) (B.transpose*X*B-g2 • 1)

def inputScaling (t : ℝ) : Matrix (Fin n ⊕ Fin b) (Fin n ⊕ Fin b) ℝ :=
  Matrix.fromBlocks 1 0 0 (t • 1)

theorem bounded_real_input_scaling (A : Mat n n) (B : Mat n b) (O : Mat o n)
    (X : Mat n n) (g t : ℝ) (ht : t≠0) :
    -boundedRealMatrix A (t • B) O X g=
      (inputScaling (n:=n) (b:=b) t).transpose*
        (-boundedRealSquared A B O X (g^2/t^2))*inputScaling t := by
  unfold boundedRealMatrix boundedRealSquared inputScaling
  rw [Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_one,Matrix.transpose_zero,Matrix.transpose_smul]
  simp only [Matrix.fromBlocks_neg,Matrix.fromBlocks_multiply,
    Matrix.one_mul,Matrix.mul_one,Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,smul_sub,smul_neg]
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.neg_apply,Matrix.sub_apply,
      Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] <;>
    field_simp [ht] <;> ring

/-- Positive semidefiniteness of the rationalized block certifies the actual
sqrt(2)-scaled injection, without numerically approximating sqrt(2). -/
theorem control_rationalization_sufficient (A : Mat n n) (P : Mat n b) (O : Mat o n)
    (X : Mat n n) (g : ℝ)
    (h : (-boundedRealSquared A P O X (g^2/2)).PosSemidef) :
    (-boundedRealMatrix A ((Real.sqrt 2) • P) O X g).PosSemidef := by
  rw [bounded_real_input_scaling A P O X g (Real.sqrt 2) (by positivity),
    Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  simpa only [Matrix.conjTranspose,star_trivial] using
    h.conjTranspose_mul_mul_same (inputScaling (n:=n) (b:=b) (Real.sqrt 2))

def intControlBoundedRealNegative (D : ℤ) (A : Matrix (Fin n) (Fin n) ℤ)
    (P : Matrix (Fin n) (Fin b) ℤ) (O : Matrix (Fin o) (Fin n) ℤ)
    (X : Matrix (Fin n) (Fin n) ℤ) (g : ℤ) :
    Matrix (Fin n ⊕ Fin b) (Fin n ⊕ Fin b) ℤ :=
  Matrix.fromBlocks ((2*D^2) • X-(2 : ℤ) • (A.transpose*X*A)-(2*D) • (O.transpose*O))
    ((-2 : ℤ) • (A.transpose*X*P)) ((-2 : ℤ) • (P.transpose*X*A))
    ((D*g^2) • (1 : Matrix (Fin b) (Fin b) ℤ)-(2 : ℤ) • (P.transpose*X*P))

theorem cleared_control_bounded_real_identity (D : ℤ) (hD : D≠0)
    (A : Matrix (Fin n) (Fin n) ℤ) (P : Matrix (Fin n) (Fin b) ℤ)
    (O : Matrix (Fin o) (Fin n) ℤ) (X : Matrix (Fin n) (Fin n) ℤ) (g : ℤ) :
    -boundedRealSquared (scaledIntMatrix D A) (scaledIntMatrix D P) (scaledIntMatrix D O)
      (scaledIntMatrix D X) (((g : ℝ)/(D : ℝ))^2/2)=
      (2*(D : ℝ)^3)⁻¹ • intRealMatrix (intControlBoundedRealNegative D A P O X g) := by
  have hd : (D : ℝ)≠0 := by exact_mod_cast hD
  have hcast : intRealMatrix (intControlBoundedRealNegative D A P O X g)=
      Matrix.fromBlocks
        ((2*(D : ℝ)^2) • intRealMatrix X-(2 : ℝ) • ((intRealMatrix A).transpose*intRealMatrix X*intRealMatrix A)-
          (2*(D : ℝ)) • ((intRealMatrix O).transpose*intRealMatrix O))
        ((-2 : ℝ) • ((intRealMatrix A).transpose*intRealMatrix X*intRealMatrix P))
        ((-2 : ℝ) • ((intRealMatrix P).transpose*intRealMatrix X*intRealMatrix A))
        (((D : ℝ)*(g : ℝ)^2) • (1 : Mat b b)-(2 : ℝ) • ((intRealMatrix P).transpose*intRealMatrix X*intRealMatrix P)) := by
    unfold intControlBoundedRealNegative
    change (Matrix.fromBlocks _ _ _ _).map (Int.castRingHom ℝ)=_
    rw [Matrix.fromBlocks_map]
    change Matrix.fromBlocks (intRealMatrix _) (intRealMatrix _) (intRealMatrix _) (intRealMatrix _)=_
    simp only [intRealMatrix_sub,intRealMatrix_smul,intRealMatrix_mul,
      intRealMatrix_transpose,intRealMatrix_one,Int.cast_pow,Int.cast_mul,Int.cast_ofNat,Int.cast_neg]
  rw [hcast]
  simp only [boundedRealSquared,scaledIntMatrix,Matrix.transpose_smul,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul]
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.neg_apply,Matrix.sub_apply,
      Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] <;>
    field_simp [hd] <;> ring

end
end Populus.ModelReduction.Certified
