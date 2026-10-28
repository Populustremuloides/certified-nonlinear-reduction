import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.IntegerMatrixCertificates

/-!
# Clearing the common dyadic denominator in the BRL matrix

This supplies the symbolic bridge from exact integer arithmetic to the same
real block matrix used in the paper's storage lemma. Denominators are kept
explicit, so a numerical checker cannot silently change norms or coefficients.
-/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {n b o : ℕ}

def intBoundedRealNegative (D : ℤ) (A : Matrix (Fin n) (Fin n) ℤ)
    (B : Matrix (Fin n) (Fin b) ℤ) (O : Matrix (Fin o) (Fin n) ℤ)
    (X : Matrix (Fin n) (Fin n) ℤ) (g : ℤ) :
    Matrix (Fin n ⊕ Fin b) (Fin n ⊕ Fin b) ℤ :=
  Matrix.fromBlocks (D^2 • X-A.transpose*X*A-D • (O.transpose*O))
    (-(A.transpose*X*B)) (-(B.transpose*X*A))
    ((D*g^2) • (1 : Matrix (Fin b) (Fin b) ℤ)-B.transpose*X*B)

theorem intRealMatrix_add {i j : Type*} [Fintype i] [Fintype j] [DecidableEq i] [DecidableEq j]
    (A B : Matrix i j ℤ) : intRealMatrix (A+B)=intRealMatrix A+intRealMatrix B := by
  ext a b
  exact Int.cast_add _ _

theorem intRealMatrix_sub {i j : Type*} [Fintype i] [Fintype j] [DecidableEq i] [DecidableEq j]
    (A B : Matrix i j ℤ) : intRealMatrix (A-B)=intRealMatrix A-intRealMatrix B := by
  ext a b
  exact Int.cast_sub _ _

theorem intRealMatrix_neg {i j : Type*} [Fintype i] [Fintype j] [DecidableEq i] [DecidableEq j]
    (A : Matrix i j ℤ) : intRealMatrix (-A)= -intRealMatrix A := by
  ext a b
  exact Int.cast_neg _

theorem intRealMatrix_smul {i j : Type*} [Fintype i] [Fintype j] [DecidableEq i] [DecidableEq j]
    (k : ℤ) (A : Matrix i j ℤ) : intRealMatrix (k • A)=(k : ℝ) • intRealMatrix A := by
  ext a b
  exact Int.cast_mul _ _

theorem intRealMatrix_one {i : Type*} [Fintype i] [DecidableEq i] :
    intRealMatrix (1 : Matrix i i ℤ)=1 := by
  ext a b
  by_cases h : a=b <;> simp [intRealMatrix,Matrix.one_apply,h]

theorem cleared_bounded_real_identity (D : ℤ) (hD : D≠0)
    (A : Matrix (Fin n) (Fin n) ℤ) (B : Matrix (Fin n) (Fin b) ℤ)
    (O : Matrix (Fin o) (Fin n) ℤ) (X : Matrix (Fin n) (Fin n) ℤ) (g : ℤ) :
    -boundedRealMatrix (scaledIntMatrix D A) (scaledIntMatrix D B) (scaledIntMatrix D O)
      (scaledIntMatrix D X) ((g : ℝ)/(D : ℝ))=
      ((D : ℝ)^3)⁻¹ • intRealMatrix (intBoundedRealNegative D A B O X g) := by
  have hd : (D : ℝ)≠0 := by exact_mod_cast hD
  have hcast : intRealMatrix (intBoundedRealNegative D A B O X g)=
      Matrix.fromBlocks
        ((D : ℝ)^2 • intRealMatrix X-(intRealMatrix A).transpose*intRealMatrix X*intRealMatrix A-
          (D : ℝ) • ((intRealMatrix O).transpose*intRealMatrix O))
        (-((intRealMatrix A).transpose*intRealMatrix X*intRealMatrix B))
        (-((intRealMatrix B).transpose*intRealMatrix X*intRealMatrix A))
        (((D : ℝ)*(g : ℝ)^2) • (1 : Mat b b)-(intRealMatrix B).transpose*intRealMatrix X*intRealMatrix B) := by
    unfold intBoundedRealNegative
    change (Matrix.fromBlocks _ _ _ _).map (Int.castRingHom ℝ)=_
    rw [Matrix.fromBlocks_map]
    change Matrix.fromBlocks (intRealMatrix _) (intRealMatrix _) (intRealMatrix _) (intRealMatrix _)=_
    simp only [intRealMatrix_sub,intRealMatrix_neg,intRealMatrix_smul,intRealMatrix_mul,
      intRealMatrix_transpose,intRealMatrix_one,Int.cast_pow,Int.cast_mul]
  rw [hcast]
  simp only [boundedRealMatrix,scaledIntMatrix,Matrix.transpose_smul,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul,
    smul_sub,smul_neg]
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.sub_apply,Matrix.add_apply,
      Matrix.smul_apply,Matrix.neg_apply,smul_eq_mul] <;>
    field_simp [hd] <;> ring

end
end Populus.ModelReduction.Certified
