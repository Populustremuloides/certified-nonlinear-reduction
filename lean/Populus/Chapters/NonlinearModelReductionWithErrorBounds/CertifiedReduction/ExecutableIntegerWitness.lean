import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ClearedBoundedReal
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.MatrixReindexing

/-!
# Executable exact-integer witnesses and their real-matrix interpretation

These definitions return Booleans using only finite integer operations. Their
soundness theorems bridge accepted witnesses to the real storage inequalities.
They do not decide positive definiteness for arbitrary exact-real inputs.
-/
namespace Populus.ModelReduction.Certified
open scoped BigOperators
variable {n b o : ℕ}

def integerPositivityCheck (Z R S : Matrix (Fin n) (Fin n) ℤ) : Bool :=
  decide (R.transpose*Z*R=S ∧ S.transpose=S ∧ ∀ i,∑ j,intOffAbs S i j<S i i)

theorem integerPositivityCheck_sound (Z R S : Matrix (Fin n) (Fin n) ℤ)
    (h : integerPositivityCheck Z R S=true) : (intRealMatrix Z).PosDef := by
  have hh : R.transpose*Z*R=S ∧ S.transpose=S ∧ ∀ i,∑ j,intOffAbs S i j<S i i :=
    of_decide_eq_true h
  exact intRealMatrix_posDef_of_certificate Z R S hh.1 hh.2.1 hh.2.2

def integerBoundedRealCheck (D : ℤ) (A : Matrix (Fin n) (Fin n) ℤ)
    (B : Matrix (Fin n) (Fin b) ℤ) (O : Matrix (Fin o) (Fin n) ℤ)
    (X RX SX : Matrix (Fin n) (Fin n) ℤ) (g : ℤ)
    (RQ SQ : Matrix (Fin (n+b)) (Fin (n+b)) ℤ) : Bool :=
  decide (0<D ∧ 0≤g) && integerPositivityCheck X RX SX &&
    integerPositivityCheck
      ((intBoundedRealNegative D A B O X g).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
      RQ SQ

theorem integerBoundedRealCheck_sound (D : ℤ) (A : Matrix (Fin n) (Fin n) ℤ)
    (B : Matrix (Fin n) (Fin b) ℤ) (O : Matrix (Fin o) (Fin n) ℤ)
    (X RX SX : Matrix (Fin n) (Fin n) ℤ) (g : ℤ)
    (RQ SQ : Matrix (Fin (n+b)) (Fin (n+b)) ℤ)
    (h : integerBoundedRealCheck D A B O X RX SX g RQ SQ=true) :
    0≤(g:ℝ)/(D:ℝ) ∧ (scaledIntMatrix D X).PosDef ∧
      (-boundedRealMatrix (scaledIntMatrix D A) (scaledIntMatrix D B) (scaledIntMatrix D O)
        (scaledIntMatrix D X) ((g:ℝ)/(D:ℝ))).PosSemidef := by
  simp only [integerBoundedRealCheck,Bool.and_eq_true] at h
  have hdg : 0<D ∧ 0≤g := of_decide_eq_true h.1.1
  have hd : 0<(D:ℝ) := by exact_mod_cast hdg.1
  have hx := integerPositivityCheck_sound X RX SX h.1.2
  have hq := integerPositivityCheck_sound _ RQ SQ h.2
  have hback := posDef_submatrix_injective _ hq finSumFinEquiv finSumFinEquiv.injective
  have hreal : (intRealMatrix (intBoundedRealNegative D A B O X g)).PosDef := by
    simpa [Matrix.submatrix,Matrix.submatrix_submatrix,Function.comp_def,intRealMatrix] using hback
  refine ⟨div_nonneg (by exact_mod_cast hdg.2) (le_of_lt hd),hx.smul (inv_pos.2 hd),?_⟩
  rw [cleared_bounded_real_identity D (ne_of_gt hdg.1)]
  exact (hreal.smul (inv_pos.2 (pow_pos hd 3))).posSemidef

end Populus.ModelReduction.Certified
