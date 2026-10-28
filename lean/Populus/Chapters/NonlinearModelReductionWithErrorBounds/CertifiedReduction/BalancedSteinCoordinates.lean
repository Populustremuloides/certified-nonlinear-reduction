import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SimilarityMatrices

/-! The paper's balancing equations transport both original Stein identities. -/
namespace Populus.ModelReduction.Certified
open Matrix
noncomputable section
variable {q m p : ℕ}

theorem balanced_controllability_stein (A P T R «Σ» : Mat q q) (B : Mat q m)
    (hRT : R*T=1) (hP : P=A*P*A.transpose+B*B.transpose)
    (hbalanced : «Σ»=T*P*T.transpose) :
    «Σ»=(T*A*R)*«Σ»*(T*A*R).transpose+(T*B)*(T*B).transpose := by
  have hRt : T.transpose*R.transpose=1 := by rw [← Matrix.transpose_mul,hRT,Matrix.transpose_one]
  have hback : R*«Σ»*R.transpose=P := by
    rw [hbalanced]
    calc
      _ = (R*T)*P*(T.transpose*R.transpose) := by noncomm_ring
      _ = P := by rw [hRT,hRt]; simp
  have hA : (T*A*R)*«Σ»*(T*A*R).transpose=T*(A*P*A.transpose)*T.transpose := by
    simp only [Matrix.transpose_mul]
    calc
      _ = T*A*(R*«Σ»*R.transpose)*A.transpose*T.transpose := by noncomm_ring
      _ = _ := by rw [hback]; noncomm_ring
  have hB : (T*B)*(T*B).transpose=T*(B*B.transpose)*T.transpose := by
    simp only [Matrix.transpose_mul,Matrix.mul_assoc]
  rw [hA,hB,← Matrix.add_mul,← Matrix.mul_add,← hP,← hbalanced]

theorem balanced_observability_stein (A Q T R «Σ» : Mat q q) (C : Mat p q)
    (hRT : R*T=1) (hQ : Q=A.transpose*Q*A+C.transpose*C)
    (hbalanced : «Σ»=R.transpose*Q*R) :
    «Σ»=(T*A*R).transpose*«Σ»*(T*A*R)+(C*R).transpose*(C*R) := by
  have hRt : T.transpose*R.transpose=1 := by rw [← Matrix.transpose_mul,hRT,Matrix.transpose_one]
  have hback : T.transpose*«Σ»*T=Q := by
    rw [hbalanced]
    calc
      _ = (T.transpose*R.transpose)*Q*(R*T) := by noncomm_ring
      _ = Q := by rw [hRT,hRt]; simp
  have hA : (T*A*R).transpose*«Σ»*(T*A*R)=R.transpose*(A.transpose*Q*A)*R := by
    simp only [Matrix.transpose_mul]
    calc
      _ = R.transpose*A.transpose*(T.transpose*«Σ»*T)*A*R := by noncomm_ring
      _ = _ := by rw [hback]; noncomm_ring
  have hC : (C*R).transpose*(C*R)=R.transpose*(C.transpose*C)*R := by
    simp only [Matrix.transpose_mul,Matrix.mul_assoc]
  rw [hA,hC,← Matrix.add_mul,← Matrix.mul_add,← hQ,← hbalanced]

end
end Populus.ModelReduction.Certified
