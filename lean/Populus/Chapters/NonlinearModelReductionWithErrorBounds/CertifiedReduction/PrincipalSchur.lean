import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.PrincipalMatrices
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ComplexEigenvectors

/-!
# A principal truncation of a diagonally dissipative Schur matrix is Schur

An eigenvector with modulus at least one would lose no energy into the
discarded coordinates. Its zero extension would therefore be an eigenvector
of the full matrix, contradicting the full Schur hypothesis.
-/
namespace Populus.ModelReduction.Certified
open Matrix
noncomputable section
variable {a b : ℕ}

theorem diagonalEnergy_nonneg (σ : Fin a → ℝ) (hσ : ∀ i,0≤σ i) (x : Rn a) :
    0≤diagonalEnergy σ x := Finset.sum_nonneg (fun i _ => mul_nonneg (hσ i) (sq_nonneg _))

theorem diagonalEnergy_pos (σ : Fin a → ℝ) (hσ : ∀ i,0<σ i) (x : Rn a)
    (hx : x≠0) : 0<diagonalEnergy σ x := by
  rw [← storage_diagonal]
  apply (Matrix.PosDef.diagonal hσ).dotProduct_mulVec_pos
  intro h
  apply hx
  ext i
  exact congrFun h i

theorem complex_energy_mass_pos (σ : Fin a → ℝ) (hσ : ∀ i,0<σ i)
    (v : Fin a → ℂ) (hv : v≠0) :
    0<diagonalEnergy σ (realPart v)+diagonalEnergy σ (imagPart v) := by
  have hr := diagonalEnergy_nonneg σ (fun i => le_of_lt (hσ i)) (realPart v)
  have hi := diagonalEnergy_nonneg σ (fun i => le_of_lt (hσ i)) (imagPart v)
  by_cases hreal : realPart v=0
  · have himag : imagPart v≠0 := by
      intro hz
      apply hv
      funext i
      apply Complex.ext
      · exact congrArg (fun z : Rn a => z i) hreal
      · exact congrArg (fun z : Rn a => z i) hz
    linarith [diagonalEnergy_pos σ hσ (imagPart v) himag]
  · linarith [diagonalEnergy_pos σ hσ (realPart v) hreal]

theorem principal_schur_of_balanced_dissipation (σ : Fin a → ℝ) (τ : ℝ)
    (hσ : ∀ i,0<σ i) (hτ : 0<τ) (A : Mat (a+b) (a+b)) (hA : Schur A)
    (hdis : ∀ z,balancedEnergy σ τ (act A z)≤balancedEnergy σ τ z) :
    Schur (principalA (a:=a) (b:=b) A) := by
  intro ζ hζ
  by_contra hn
  have hζnorm : 1≤‖ζ‖ := le_of_not_gt hn
  obtain ⟨v,hv,he⟩ := (matrix_mem_spectrum_iff_eigenvector _ ζ).1 hζ
  let xr := realPart v
  let xi := imagPart v
  let yr := act A (join xr (0 : Rn b))
  let yi := act A (join xi (0 : Rn b))
  have her : take yr=ζ.re • xr-ζ.im • xi := by
    rw [← act_principalA]
    exact realPart_eigenvector _ v ζ he
  have hei : take yi=ζ.im • xr+ζ.re • xi := by
    rw [← act_principalA]
    exact imagPart_eigenvector _ v ζ he
  have hr := hdis (join xr (0 : Rn b))
  have hi := hdis (join xi (0 : Rn b))
  have hrot := diagonalEnergy_complex_rotation σ ζ xr xi
  have hmass := complex_energy_mass_pos σ hσ v hv
  have hhead (z : Rn (a+b)) : balancedEnergy σ τ z=
      diagonalEnergy σ (take z)+τ*‖drop z‖^2 := rfl
  have hinj (z : Rn a) : balancedEnergy σ τ (join z (0 : Rn b))=diagonalEnergy σ z := by
    simp [balancedEnergy,diagonalEnergy]
  rw [hinj,hhead,her] at hr
  rw [hinj,hhead,hei] at hi
  have hsq : 1≤‖ζ‖^2 := by nlinarith [norm_nonneg ζ]
  have hscale : diagonalEnergy σ xr+diagonalEnergy σ xi≤
      ‖ζ‖^2*(diagonalEnergy σ xr+diagonalEnergy σ xi) :=
    (le_mul_iff_one_le_left hmass).2 hsq
  have htail : τ*(‖drop yr‖^2+‖drop yi‖^2)≤0 := by linarith
  have hsum : ‖drop yr‖^2+‖drop yi‖^2≤0 := nonpos_of_mul_nonpos_right htail hτ
  have hyr : drop yr=0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖drop yi‖,norm_nonneg (drop yr)])
  have hyi : drop yi=0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖drop yr‖,norm_nonneg (drop yi)])
  let w : Fin (a+b) → ℂ := Fin.addCases v (fun _ => 0)
  have hw : w≠0 := by
    intro hz
    apply hv
    funext i
    simpa [w] using congrFun hz (Fin.castAdd b i)
  have hefull : complexify A *ᵥ w=ζ • w := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hj := congrFun he j
      simpa [complexify,Matrix.mulVec,dotProduct,w,principalA,Fin.sum_univ_add] using hj
    · apply Complex.ext
      · have hj := congrArg (fun z : Rn b => z j) hyr
        simpa [yr,xr,drop,act,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,
          complexify,w,join,realPart,Fin.sum_univ_add] using hj
      · have hj := congrArg (fun z : Rn b => z j) hyi
        simpa [yi,xi,drop,act,Matrix.toEuclideanLin,Matrix.mulVec,dotProduct,
          complexify,w,join,imagPart,Fin.sum_univ_add] using hj
  exact (not_lt_of_ge hζnorm) (hA ζ ((matrix_mem_spectrum_iff_eigenvector _ ζ).2 ⟨w,hw,hefull⟩))

end
end Populus.ModelReduction.Certified
