import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.DiagonalSteinStorage
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-! Real and imaginary Euclidean coordinates of actual complex eigenvectors. -/
namespace Populus.ModelReduction.Certified
open Matrix
open scoped BigOperators
noncomputable section
variable {d : ℕ}

def realPart (v : Fin d → ℂ) : Rn d := WithLp.toLp 2 (fun i => (v i).re)
def imagPart (v : Fin d → ℂ) : Rn d := WithLp.toLp 2 (fun i => (v i).im)

theorem matrix_mem_spectrum_iff_eigenvector (A : Matrix (Fin d) (Fin d) ℂ) (ζ : ℂ) :
    ζ∈spectrum ℂ A ↔ ∃ v : Fin d → ℂ,v≠0 ∧ A *ᵥ v=ζ • v := by
  rw [← Matrix.spectrum_toLin']
  constructor
  · intro h
    obtain ⟨v,hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr h).exists_hasEigenvector
    exact ⟨v,hv.2,hv.apply_eq_smul⟩
  · rintro ⟨v,hv,he⟩
    apply Module.End.hasEigenvalue_iff_mem_spectrum.mp
    exact Module.End.hasEigenvalue_of_hasEigenvector (show Module.End.HasEigenvector A.toLin' ζ v from ⟨Module.End.mem_eigenspace_iff.mpr he,hv⟩)

theorem realPart_eigenvector (A : Mat d d) (v : Fin d → ℂ) (ζ : ℂ)
    (h : complexify A *ᵥ v=ζ • v) :
    act A (realPart v)=ζ.re • realPart v-ζ.im • imagPart v := by
  ext i
  have hi := congrArg (fun w : Fin d → ℂ => (w i).re) h
  simpa [act,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,complexify,
    realPart,imagPart,Complex.mul_re] using hi

theorem imagPart_eigenvector (A : Mat d d) (v : Fin d → ℂ) (ζ : ℂ)
    (h : complexify A *ᵥ v=ζ • v) :
    act A (imagPart v)=ζ.im • realPart v+ζ.re • imagPart v := by
  ext i
  have hi := congrArg (fun w : Fin d → ℂ => (w i).im) h
  simpa [act,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,complexify,
    realPart,imagPart,Complex.mul_im,add_comm,mul_comm] using hi

theorem diagonalEnergy_complex_rotation (σ : Fin d → ℝ) (ζ : ℂ) (x y : Rn d) :
    diagonalEnergy σ (ζ.re • x-ζ.im • y)+diagonalEnergy σ (ζ.im • x+ζ.re • y)=
      ‖ζ‖^2*(diagonalEnergy σ x+diagonalEnergy σ y) := by
  simp only [diagonalEnergy,← Finset.sum_add_distrib,Finset.mul_sum,
    Complex.sq_norm,Complex.normSq_apply,WithLp.ofLp_sub,WithLp.ofLp_add,
    WithLp.ofLp_smul,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end Populus.ModelReduction.Certified
