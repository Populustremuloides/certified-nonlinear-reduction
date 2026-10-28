import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ConstructedCertificate

/-!
# Finite arithmetic evaluation of a valid certificate

Once the finite matrix witnesses have been certified, the numerical bound
is this fixed arithmetic expression in eleven scalar witness values. The
interpreter is executable for any executable field, including ℚ. Its real
interpretation is proved equal to the mathematical certificate on valid data.
Exact integer witness acceptance is treated in ExecutableIntegerWitness;
arbitrary-real comparison and IEEE arithmetic are not assumed executable.
-/
namespace Populus.ModelReduction.Certified

inductive CertificateExpr (n : ℕ) where
  | var : Fin n → CertificateExpr n
  | one : CertificateExpr n
  | add : CertificateExpr n → CertificateExpr n → CertificateExpr n
  | sub : CertificateExpr n → CertificateExpr n → CertificateExpr n
  | mul : CertificateExpr n → CertificateExpr n → CertificateExpr n
  | inv : CertificateExpr n → CertificateExpr n
  deriving Repr

def CertificateExpr.eval {n : ℕ} {K : Type*} [DivisionRing K]
    (s : Fin n → K) : CertificateExpr n → K
  | .var i => s i
  | .one => 1
  | .add a b => a.eval s+b.eval s
  | .sub a b => a.eval s-b.eval s
  | .mul a b => a.eval s*b.eval s
  | .inv a => (a.eval s)⁻¹

def finiteCertificateExpression : CertificateExpr 11 :=
  let Γ : CertificateExpr 11 := .mul (.add (.var 0) (.var 1)) (.inv (.sub .one (.var 2)))
  let Γ_hat : CertificateExpr 11 := .mul (.add (.var 5) (.var 6)) (.inv (.sub .one (.var 7)))
  let ε : CertificateExpr 11 := .add (.mul (.var 3) Γ) (.var 4)
  let ε_hat : CertificateExpr 11 := .add (.mul (.var 8) Γ_hat) (.var 9)
  .add (.add ε (.var 10)) ε_hat

noncomputable section
variable {q r m p p_u p_z : ℕ}

def certificateScalarValues (R : ReductionWitnesses q r) : Fin 11 → ℝ :=
  ![R.full.bounds.g_u,R.full.bounds.g_δu,R.full.bounds.g_δz,
    R.full.bounds.h_δz,R.full.bounds.h_δu,
    R.reduced.bounds.g_u,R.reduced.bounds.g_δu,R.reduced.bounds.g_δz,
    R.reduced.bounds.h_δz,R.reduced.bounds.h_δu,R.nominal.g]

theorem finite_certificate_expression_eq_bound (R : ReductionWitnesses q r) :
    finiteCertificateExpression.eval (certificateScalarValues R)=R.bound := by
  simp [finiteCertificateExpression,CertificateExpr.eval,certificateScalarValues,
    ReductionWitnesses.bound,GainBounds.ε,GainBounds.Γ,div_eq_mul_inv]

theorem certificate_evaluation_from_valid_witnesses (R : ReductionWitnesses q r)
    (N : NominalMatrices q m p p_u p_z) (W_r : Mat r q) (V_r : Mat q r)
    (h : R.Valid N W_r V_r) :
    R.B_r N W_r V_r=ENNReal.ofReal
      (finiteCertificateExpression.eval (certificateScalarValues R)) := by
  rw [finite_certificate_expression_eq_bound,R.B_r_eq_of_valid N W_r V_r h]

end
end Populus.ModelReduction.Certified
