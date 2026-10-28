import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.BalancedPrincipalGain

/-!
# A principal balanced reduction bound derived from literal Stein inequalities

No gain hypothesis for the error channel is assumed. The storage inequalities
are derived from the controllability/observability matrices and then telescoped
along the actual full and truncated recurrences.
-/
namespace Populus.ModelReduction.Certified
open scoped BigOperators ENNReal
noncomputable section
variable {a b m p : ℕ}

theorem diagonalEnergy_balanced (σ : Fin a → ℝ) (τ : ℝ) (z : Rn (a+b)) :
    diagonalEnergy (Fin.addCases σ (fun _ : Fin b => τ)) z=balancedEnergy σ τ z := by
  simp [diagonalEnergy,balancedEnergy,Fin.sum_univ_add,take,drop,
    EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]

theorem balanced_principal_error_from_stein (σ : Fin a → ℝ) (τ : ℝ)
    (hσ : ∀ i,0<σ i) (hτ : 0<τ)
    (A : Mat (a+b) (a+b)) (B : Mat (a+b) m) (C : Mat p (a+b))
    (hP : (Matrix.diagonal (Fin.addCases σ (fun _ : Fin b => τ))-
      A*Matrix.diagonal (Fin.addCases σ (fun _ : Fin b => τ))*A.transpose-B*B.transpose).PosSemidef)
    (hQ : (Matrix.diagonal (Fin.addCases σ (fun _ : Fin b => τ))-
      A.transpose*Matrix.diagonal (Fin.addCases σ (fun _ : Fin b => τ))*A-C.transpose*C).PosSemidef) :
    inducedGain (fun u k => act C (linearResponse A B u k-
      join (balancedPrincipalResponse (b:=b) A B u k) (0 : Rn b)))≤ENNReal.ofReal (2*τ) := by
  apply balanced_principal_induced_gain σ τ (fun i => le_of_lt (hσ i)) hτ A B C
  · intro z
    simpa only [diagonalEnergy_balanced] using observability_stein_storage _ A C hQ z
  · intro z u
    have hρ : ∀ i : Fin (a+b),(0:ℝ)<Fin.addCases σ (fun _ : Fin b => τ) i := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using hσ j
      · simpa using hτ
    have hi := controllability_stein_storage _ hρ A B hP z u
    have he : (fun i => (Fin.addCases σ (fun _ : Fin b => τ) i)⁻¹)=
        Fin.addCases (fun i => (σ i)⁻¹) (fun _ : Fin b => τ⁻¹) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    rw [he] at hi
    simpa only [diagonalEnergy_balanced] using hi

end
end Populus.ModelReduction.Certified
