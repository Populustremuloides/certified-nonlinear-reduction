import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.StorageLyapunovSchur
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.CertificateArithmetic

/-!
# The complete certificate follows from finite storage checks

The state-port matrix inequalities already imply both nominal Schur facts.
The only further geometric check is injectivity of reconstruction, supplied
by W_r V_r=I in the exact projection case or by the stored Gram certificate.
All nonlinear conclusions then follow for every compatible normalized map.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {q r m p p_u p_z : ℕ}

theorem reduction_witnesses_valid_from_storage_checks
    (N : NominalMatrices q m p p_u p_z) (W_r : Mat r q) (V_r : Mat q r)
    (R : ReductionWitnesses q r) (hV : Function.Injective (act V_r))
    (hfull : R.full.Valid N (1 : Mat q q))
    (hred : R.reduced.Valid (N.reduced W_r V_r) V_r)
    (hnom : R.nominal.Valid (errorA N.A (N.reduced W_r V_r).A)
      (errorB N.B_u (N.reduced W_r V_r).B_u) (errorC N.C (N.reduced W_r V_r).C)) :
    R.Valid N W_r V_r := by
  exact ⟨schur_of_state_storage N.A N.B_δz (1 : Mat q q) R.full.state_δz hfull.2.2.1
      (by intro x y h; simpa only [act_one] using h),
    schur_of_state_storage (N.reduced W_r V_r).A (N.reduced W_r V_r).B_δz V_r
      R.reduced.state_δz hred.2.2.1 hV,hV,hfull,hred,hnom⟩

theorem certificate_evaluation_from_storage_checks
    (N : NominalMatrices q m p p_u p_z) (W_r : Mat r q) (V_r : Mat q r)
    (R : ReductionWitnesses q r) (hV : Function.Injective (act V_r))
    (hfull : R.full.Valid N (1 : Mat q q))
    (hred : R.reduced.Valid (N.reduced W_r V_r) V_r)
    (hnom : R.nominal.Valid (errorA N.A (N.reduced W_r V_r).A)
      (errorB N.B_u (N.reduced W_r V_r).B_u) (errorC N.C (N.reduced W_r V_r).C)) :
    R.B_r N W_r V_r=ENNReal.ofReal
      (finiteCertificateExpression.eval (certificateScalarValues R)) :=
  certificate_evaluation_from_valid_witnesses R N W_r V_r
    (reduction_witnesses_valid_from_storage_checks N W_r V_r R hV hfull hred hnom)

end
end Populus.ModelReduction.Certified
