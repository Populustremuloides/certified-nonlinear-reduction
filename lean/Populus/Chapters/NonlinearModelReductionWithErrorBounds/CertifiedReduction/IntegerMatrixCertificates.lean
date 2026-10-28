import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.DyadicMatrices
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.StrictDiagonalDominance
import Mathlib.Data.Real.StarOrdered

/-!
# Kernel-checkable integer certificates for real matrix positivity

All frozen coefficients are dyadic, so a common positive denominator clears
all BRL blocks. Proposed congruences are arbitrary integer matrices; only
exact multiplication, symmetry and strict row inequalities are checked.
-/
namespace Populus.ModelReduction.Certified
open scoped BigOperators
noncomputable section
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def intRealMatrix (Z : Matrix n m ℤ) : Matrix n m ℝ := Z.map (Int.castRingHom ℝ)
def intOffAbs (Z : Matrix n n ℤ) (i j : n) : ℤ :=
  if i=j then 0 else |Z i j|

theorem intRealMatrix_mul (Z : Matrix n m ℤ)
    {k : Type*} [Fintype k] [DecidableEq k] (Y : Matrix m k ℤ) :
    intRealMatrix (Z*Y)=intRealMatrix Z*intRealMatrix Y := Matrix.map_mul

theorem intRealMatrix_transpose (Z : Matrix n m ℤ) :
    intRealMatrix Z.transpose=(intRealMatrix Z).transpose := rfl

theorem offAbs_intRealMatrix (Z : Matrix n n ℤ) (i j : n) :
    offAbs (intRealMatrix Z) i j=(intOffAbs Z i j : ℝ) := by
  by_cases h : i=j <;> simp [offAbs,intOffAbs,intRealMatrix,h]

/-- An exact integer congruence and integer diagonal-dominance inequalities
certify positive definiteness after interpreting the coefficients as reals. -/
theorem intRealMatrix_posDef_of_certificate
    (Z R S : Matrix n n ℤ)
    (hprod : R.transpose*Z*R=S) (hs : S.transpose=S)
    (hdom : ∀ i,∑ j,intOffAbs S i j<S i i) : (intRealMatrix Z).PosDef := by
  apply posDef_of_checked_diagonal_congruence (intRealMatrix Z) (intRealMatrix R) (intRealMatrix S)
  · rw [← intRealMatrix_transpose,← intRealMatrix_mul,← intRealMatrix_mul,hprod]
  · rw [← intRealMatrix_transpose,hs]
  · intro i
    simp_rw [offAbs_intRealMatrix]
    change (∑ j,(intOffAbs S i j : ℝ))<(S i i : ℝ)
    exact_mod_cast hdom i

/-- Scaled integer matrices over an arbitrary nonzero common denominator. -/
def scaledIntMatrix (D : ℤ) (Z : Matrix n m ℤ) : Matrix n m ℝ :=
  (D : ℝ)⁻¹ • intRealMatrix Z

theorem scaledIntMatrix_posDef_of_certificate (D : ℤ) (hD : 0<D)
    (Z R S : Matrix n n ℤ)
    (hprod : R.transpose*Z*R=S) (hs : S.transpose=S)
    (hdom : ∀ i,∑ j,intOffAbs S i j<S i i) : (scaledIntMatrix D Z).PosDef := by
  have hd : 0<(D : ℝ) := by exact_mod_cast hD
  exact (intRealMatrix_posDef_of_certificate Z R S hprod hs hdom).smul (inv_pos.2 hd)

end
end Populus.ModelReduction.Certified
