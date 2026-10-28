import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.IntegerMatrixCertificates

/-! Equivalence of flat coordinate arithmetic and the paper's stacked block indices. -/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {a b : Type*} [Fintype a] [Fintype b]

theorem posDef_submatrix_injective (M : Matrix a a ℝ) (hM : M.PosDef)
    (e : b → a) (he : Function.Injective e) : (M.submatrix e e).PosDef := by
  refine ⟨hM.1.submatrix e,?_⟩
  intro x hx
  have hne : x.mapDomain e≠0 := by
    intro hz
    apply hx
    apply Finsupp.mapDomain_injective he
    simpa using hz
  simpa [Finsupp.sum_mapDomain_index,add_mul,mul_add] using hM.2 hne

variable {n m : ℕ}
def sumIndexMatrix (Z : Matrix (Fin (n+m)) (Fin (n+m)) ℤ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℤ :=
  Z.submatrix finSumFinEquiv finSumFinEquiv

theorem sumIndexMatrix_mul (Z R : Matrix (Fin (n+m)) (Fin (n+m)) ℤ) :
    sumIndexMatrix (Z*R)=sumIndexMatrix Z*sumIndexMatrix R := by
  exact (Matrix.submatrix_mul_equiv Z R finSumFinEquiv finSumFinEquiv finSumFinEquiv).symm

theorem sumIndexMatrix_transpose (Z : Matrix (Fin (n+m)) (Fin (n+m)) ℤ) :
    sumIndexMatrix Z.transpose=(sumIndexMatrix Z).transpose := rfl

theorem intReal_sumIndexMatrix_posDef (Z : Matrix (Fin (n+m)) (Fin (n+m)) ℤ)
    (hZ : (intRealMatrix Z).PosDef) : (intRealMatrix (sumIndexMatrix Z)).PosDef := by
  exact posDef_submatrix_injective (intRealMatrix Z) hZ finSumFinEquiv finSumFinEquiv.injective

end
end Populus.ModelReduction.Certified
