import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ExecutableIntegerWitness
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ControlBoundedReal

/-! Executable exact-integer checks for the actual sqrt(2)-scaled control port. -/
namespace Populus.ModelReduction.Certified
variable {n b o : ℕ}

def integerControlBoundedRealCheck (D : ℤ) (A : Matrix (Fin n) (Fin n) ℤ)
    (P : Matrix (Fin n) (Fin b) ℤ) (O : Matrix (Fin o) (Fin n) ℤ)
    (X RX SX : Matrix (Fin n) (Fin n) ℤ) (g : ℤ)
    (RQ SQ : Matrix (Fin (n+b)) (Fin (n+b)) ℤ) : Bool :=
  decide (0<D ∧ 0≤g) && integerPositivityCheck X RX SX &&
    integerPositivityCheck
      ((intControlBoundedRealNegative D A P O X g).submatrix
        (finSumFinEquiv : Fin n ⊕ Fin b ≃ Fin (n+b)).symm
        (finSumFinEquiv : Fin n ⊕ Fin b ≃ Fin (n+b)).symm) RQ SQ

theorem integerControlBoundedRealCheck_sound (D : ℤ) (A : Matrix (Fin n) (Fin n) ℤ)
    (P : Matrix (Fin n) (Fin b) ℤ) (O : Matrix (Fin o) (Fin n) ℤ)
    (X RX SX : Matrix (Fin n) (Fin n) ℤ) (g : ℤ)
    (RQ SQ : Matrix (Fin (n+b)) (Fin (n+b)) ℤ)
    (h : integerControlBoundedRealCheck D A P O X RX SX g RQ SQ=true) :
    0≤(g:ℝ)/(D:ℝ) ∧ (scaledIntMatrix D X).PosDef ∧
      (-boundedRealMatrix (scaledIntMatrix D A) ((Real.sqrt 2) • scaledIntMatrix D P)
        (scaledIntMatrix D O) (scaledIntMatrix D X) ((g:ℝ)/(D:ℝ))).PosSemidef := by
  simp only [integerControlBoundedRealCheck,Bool.and_eq_true] at h
  have hdg : 0<D ∧ 0≤g := of_decide_eq_true h.1.1
  have hd : 0<(D:ℝ) := by exact_mod_cast hdg.1
  have hx := integerPositivityCheck_sound X RX SX h.1.2
  have hq := integerPositivityCheck_sound _ RQ SQ h.2
  have hback := posDef_submatrix_injective _ hq finSumFinEquiv finSumFinEquiv.injective
  have hreal : (intRealMatrix (intControlBoundedRealNegative D A P O X g)).PosDef := by
    simpa [Matrix.submatrix,Matrix.submatrix_submatrix,Function.comp_def,intRealMatrix] using hback
  refine ⟨div_nonneg (by exact_mod_cast hdg.2) (le_of_lt hd),hx.smul (inv_pos.2 hd),?_⟩
  apply control_rationalization_sufficient
  rw [cleared_control_bounded_real_identity D (ne_of_gt hdg.1)]
  exact (hreal.smul (inv_pos.2 (mul_pos (by norm_num) (pow_pos hd 3)))).posSemidef

end Populus.ModelReduction.Certified
