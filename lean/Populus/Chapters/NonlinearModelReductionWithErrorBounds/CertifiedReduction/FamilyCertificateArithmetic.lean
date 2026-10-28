import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.NeuralFamily
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.FiniteMatrixProtocol

/-! The universal family's finite certificate is the proved arithmetic expression. -/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {n q r m p : ℕ}

theorem Θ.certificate_evaluation (θ : Θ n q r m p) (hfinite : θ.𝓑_r≠⊤) :
    θ.𝓑_r=ENNReal.ofReal (finiteCertificateExpression.eval (certificateScalarValues θ.witnesses)) :=
  certificate_evaluation_from_valid_witnesses θ.witnesses θ.nominal θ.W_r θ.V_r
    ((θ.witnesses.B_r_finite_iff θ.nominal θ.W_r θ.V_r).1 hfinite)

end
end Populus.ModelReduction.Certified
