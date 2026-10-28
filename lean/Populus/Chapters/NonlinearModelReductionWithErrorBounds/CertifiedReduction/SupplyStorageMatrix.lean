import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.HilbertLinearRealization
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.Real.StarOrdered

/-!
# The maximized supply is an actual finite-dimensional quadratic storage

The maximizing input is a bounded linear function of the initial state, so
its value is represented by a symmetric bilinear form. Its matrix is taken in
the actual standard Euclidean coordinates used by the manuscript.
-/
namespace Populus.ModelReduction.Certified
open scoped InnerProductSpace
noncomputable section
variable {U Y Z X : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]

def energyBilin (L : X →L[ℝ] Y) (R : X →L[ℝ] Z) (K : X →L[ℝ] U) (γ α : ℝ) :
    LinearMap.BilinForm ℝ X := LinearMap.mk₂ ℝ
  (fun x y => ⟪L x, L y⟫_ℝ + α * ⟪R x, R y⟫_ℝ - γ^2 * ⟪K x, K y⟫_ℝ)
  (by intro x y z; simp only [map_add,inner_add_left]; ring)
  (by intro t x y; simp only [map_smul,real_inner_smul_left,smul_eq_mul]; ring)
  (by intro x y z; simp only [map_add,inner_add_right]; ring)
  (by intro t x y; simp only [map_smul,real_inner_smul_right,smul_eq_mul]; ring)

@[simp] theorem energyBilin_apply (L : X →L[ℝ] Y) (R : X →L[ℝ] Z) (K : X →L[ℝ] U)
    (γ α : ℝ) (x y : X) : energyBilin L R K γ α x y=
      ⟪L x, L y⟫_ℝ + α * ⟪R x, R y⟫_ℝ - γ^2 * ⟪K x, K y⟫_ℝ := rfl

theorem energyBilin_symmetric (L : X →L[ℝ] Y) (R : X →L[ℝ] Z) (K : X →L[ℝ] U)
    (γ α : ℝ) (x y : X) : energyBilin L R K γ α x y=energyBilin L R K γ α y x := by
  simp only [energyBilin_apply,real_inner_comm]

variable {d : ℕ}

def standardMatrix (B : LinearMap.BilinForm ℝ (Rn d)) : Mat d d :=
  LinearMap.BilinForm.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis B

theorem standardMatrix_storage (B : LinearMap.BilinForm ℝ (Rn d)) (x : Rn d) :
    storage (standardMatrix B) x=B x x := by
  have h := B.apply_eq_dotProduct_toMatrix_mulVec (EuclideanSpace.basisFun (Fin d) ℝ).toBasis x x
  exact h.symm

theorem standardMatrix_hermitian (B : LinearMap.BilinForm ℝ (Rn d)) (hsym : ∀ x y, B x y=B y x) :
    (standardMatrix B).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simpa only [standardMatrix,LinearMap.BilinForm.toMatrix_apply,star_trivial] using
    hsym ((EuclideanSpace.basisFun (Fin d) ℝ) j) ((EuclideanSpace.basisFun (Fin d) ℝ) i)

variable [CompleteSpace U] [CompleteSpace Y] [CompleteSpace Z]

def optimalValueBilin (T : U →L[ℝ] Y) (S : U →L[ℝ] Z)
    (Q : X →L[ℝ] Y) (R : X →L[ℝ] Z) (γ α : ℝ)
    (h : IsCoercive (supplyPenalty T S γ α)) : LinearMap.BilinForm ℝ X :=
  energyBilin (Q+T.comp (optimalSupplyInput T S Q R γ α h))
    (R+S.comp (optimalSupplyInput T S Q R γ α h)) (optimalSupplyInput T S Q R γ α h) γ α

theorem optimalValueBilin_eq_supply (T : U →L[ℝ] Y) (S : U →L[ℝ] Z)
    (Q : X →L[ℝ] Y) (R : X →L[ℝ] Z) (γ α : ℝ)
    (h : IsCoercive (supplyPenalty T S γ α)) (x : X) :
    optimalValueBilin T S Q R γ α h x x=
      supplyValue T S Q R γ α x (optimalSupplyInput T S Q R γ α h x) := by
  simp only [optimalValueBilin,energyBilin_apply,real_inner_self_eq_norm_sq,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,supplyValue]

end
end Populus.ModelReduction.Certified
