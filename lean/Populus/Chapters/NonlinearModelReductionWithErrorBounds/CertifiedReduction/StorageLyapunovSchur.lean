import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ComplexEigenvectors
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.MatrixWitnesses

/-!
# A checked state-storage witness also certifies nominal Schur stability

The zero-port specialization supplies a strict observable quadratic loss.
Real and imaginary parts of any putative nondecaying complex eigenvector
contradict that loss. No numerical eigenvalue calculation is assumed.
-/
namespace Populus.ModelReduction.Certified
open Matrix
noncomputable section
variable {d q b : ℕ}

theorem storage_scalar_rotation (X : Mat d d) (a b : ℝ) (x y : Rn d) :
    storage X (a • x-b • y)+storage X (b • x+a • y)=
      (a^2+b^2)*(storage X x+storage X y) := by
  simp only [storage,WithLp.ofLp_add,WithLp.ofLp_sub,WithLp.ofLp_smul,
    Matrix.mulVec_add,Matrix.mulVec_sub,Matrix.mulVec_smul,
    add_dotProduct,sub_dotProduct,smul_dotProduct,dotProduct_add,dotProduct_sub,
    dotProduct_smul,smul_eq_mul]
  ring

theorem storage_nonneg_of_posDef (X : Mat d d) (hX : X.PosDef) (x : Rn d) : 0≤storage X x := by
  simpa only [storage,star_trivial] using hX.posSemidef.dotProduct_mulVec_nonneg (x : Fin d → ℝ)

theorem storage_pos_of_posDef (X : Mat d d) (hX : X.PosDef) (x : Rn d) (hx : x≠0) :
    0<storage X x := by
  apply hX.dotProduct_mulVec_pos
  intro h
  apply hx
  ext i
  exact congrFun h i

theorem complex_storage_mass_pos (X : Mat d d) (hX : X.PosDef)
    (v : Fin d → ℂ) (hv : v≠0) :
    0<storage X (realPart v)+storage X (imagPart v) := by
  have hr := storage_nonneg_of_posDef X hX (realPart v)
  have hi := storage_nonneg_of_posDef X hX (imagPart v)
  by_cases hreal : realPart v=0
  · have himag : imagPart v≠0 := by
      intro hz
      apply hv
      funext i
      apply Complex.ext
      · exact congrArg (fun z : Rn d => z i) hreal
      · exact congrArg (fun z : Rn d => z i) hz
    linarith [storage_pos_of_posDef X hX (imagPart v) himag]
  · linarith [storage_pos_of_posDef X hX (realPart v) hreal]

theorem schur_of_observable_quadratic_dissipation (A : Mat d d) (O : Mat q d) (X : Mat d d)
    (hX : X.PosDef) (hO : Function.Injective (act O))
    (hdis : ∀ z,storage X (act A z)+‖act O z‖^2≤storage X z) : Schur A := by
  intro ζ hζ
  by_contra hn
  have hnorm : 1≤‖ζ‖ := le_of_not_gt hn
  obtain ⟨v,hv,he⟩ := (matrix_mem_spectrum_iff_eigenvector _ ζ).1 hζ
  have hr := hdis (realPart v)
  have hi := hdis (imagPart v)
  rw [realPart_eigenvector A v ζ he] at hr
  rw [imagPart_eigenvector A v ζ he] at hi
  have hrot := storage_scalar_rotation X ζ.re ζ.im (realPart v) (imagPart v)
  have hmass := complex_storage_mass_pos X hX v hv
  have hsq : 1≤ζ.re^2+ζ.im^2 := by
    have hh : 1≤‖ζ‖^2 := by nlinarith [norm_nonneg ζ]
    rw [Complex.sq_norm,Complex.normSq_apply] at hh
    nlinarith
  have hscale : storage X (realPart v)+storage X (imagPart v)≤
      (ζ.re^2+ζ.im^2)*(storage X (realPart v)+storage X (imagPart v)) :=
    (le_mul_iff_one_le_left hmass).2 hsq
  have hsum : ‖act O (realPart v)‖^2+‖act O (imagPart v)‖^2≤0 := by linarith
  have hreal : realPart v=0 := hO (by
    rw [act_zero]
    exact norm_eq_zero.mp (by nlinarith [sq_nonneg ‖act O (imagPart v)‖,norm_nonneg (act O (realPart v))]))
  have himag : imagPart v=0 := hO (by
    rw [act_zero]
    exact norm_eq_zero.mp (by nlinarith [sq_nonneg ‖act O (realPart v)‖,norm_nonneg (act O (imagPart v))]))
  apply hv
  funext i
  apply Complex.ext
  · exact congrArg (fun z : Rn d => z i) hreal
  · exact congrArg (fun z : Rn d => z i) himag

theorem schur_of_state_storage (A : Mat d d) (B : Mat d b) (O : Mat q d)
    (U : StorageUpper d) (hU : U.Valid A B O) (hO : Function.Injective (act O)) : Schur A := by
  apply schur_of_observable_quadratic_dissipation A O U.X hU.2.1 hO
  intro z
  have h := bounded_real_one_step A B O U.X U.g hU.2.2 z (0 : Rn b)
  simpa only [act_zero,add_zero,norm_zero,zero_pow (by decide : 2≠0),mul_zero] using h

end
end Populus.ModelReduction.Certified
