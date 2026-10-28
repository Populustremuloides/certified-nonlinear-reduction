import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.RealSchur

namespace Populus.ModelReduction.Certified
open scoped Matrix.Norms.L2Operator
noncomputable section

/-- Euclidean matrix action is bounded by its actual induced operator norm. -/
theorem norm_act_le {n m : ℕ} (A : Mat n m) (x : Rn m) : ‖act A x‖≤‖A‖*‖x‖ :=
  Matrix.l2_opNorm_mulVec A x

end
end Populus.ModelReduction.Certified
