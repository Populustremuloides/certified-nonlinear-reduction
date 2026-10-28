import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ReductionComparison
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.MatrixWitnesses
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.NominalError

/-!
# The complete extended finite-matrix reduction certificate

Paper: `def:constructed-certificate` and `prop:certificate`. The extended value
is infinity on invalid witnesses. On valid finite matrix witnesses it equals
`ε + b_r⁰ + ε_hat`. No residual-network weights enter either the validity
checks or this value. The classical real-valued definition formalizes the
mathematical certificate. CertificateArithmetic and FiniteMatrixProtocol
prove its finite arithmetic evaluation from valid storage witnesses;
ExecutableIntegerWitness and ExecutableControlWitness supply sound
integer/dyadic witness checks. No IEEE execution theorem is asserted.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {q r m p p_u p_z : ℕ}

structure ReductionWitnesses (q r : ℕ) where
  full : MatrixGainWitnesses q
  reduced : MatrixGainWitnesses r
  nominal : StorageUpper (q+r)

namespace ReductionWitnesses

def Valid (R : ReductionWitnesses q r) (N : NominalMatrices q m p p_u p_z)
    (W_r : Mat r q) (V_r : Mat q r) : Prop :=
  Schur N.A ∧ Schur (N.reduced W_r V_r).A ∧ Function.Injective (act V_r) ∧
  R.full.Valid N (1 : Mat q q) ∧ R.reduced.Valid (N.reduced W_r V_r) V_r ∧
  R.nominal.Valid (errorA N.A (N.reduced W_r V_r).A)
    (errorB N.B_u (N.reduced W_r V_r).B_u) (errorC N.C (N.reduced W_r V_r).C)

def bound (R : ReductionWitnesses q r) : ℝ := R.full.bounds.ε+R.nominal.g+R.reduced.bounds.ε

def B_r (R : ReductionWitnesses q r) (N : NominalMatrices q m p p_u p_z)
    (W_r : Mat r q) (V_r : Mat q r) : ℝ≥0∞ := by
  classical
  exact if R.Valid N W_r V_r then ENNReal.ofReal R.bound else ⊤

theorem B_r_finite_iff (R : ReductionWitnesses q r) (N : NominalMatrices q m p p_u p_z)
    (W_r : Mat r q) (V_r : Mat q r) : R.B_r N W_r V_r≠⊤ ↔ R.Valid N W_r V_r := by
  by_cases h : R.Valid N W_r V_r <;> simp [B_r,h]

/-- Fixed matrices, projection and witnesses imply precisely one unchanged
certificate for every choice of full or reduced residual-network weights. -/
theorem B_r_eq_of_valid (R : ReductionWitnesses q r) (N : NominalMatrices q m p p_u p_z)
    (W_r : Mat r q) (V_r : Mat q r) (h : R.Valid N W_r V_r) :
    R.B_r N W_r V_r=ENNReal.ofReal R.bound := by simp [B_r,h]

end ReductionWitnesses

/-- **Paper Proposition `prop:certificate`: Certified nonlinear state reduction.**

Finiteness of the constructed extended certificate gives every requirement
of Definition 3, with stronger exponential stability. All gain premises are
derived from the explicit finite storage matrices. The two residual choices
may differ, giving the paper's uniform residual-replacement conclusion.
The ordinary reduction is the specialization with equal residual choices.
-/
theorem certified_nonlinear_state_reduction [NeZero q] [NeZero r]
    (N : NominalMatrices q m p p_u p_z) (W_r : Mat r q) (V_r : Mat q r)
    (R : ReductionWitnesses q r) (hfinite : R.B_r N W_r V_r≠⊤)
    («Δ_z¹» «Δ_z²» : Rn q → Rn p_z) («Δ_u¹» «Δ_u²» : Rn q → Rn m → Rn p_u)
    («hz¹» : ∀ z, ‖«Δ_z¹» z‖ ≤ ‖z‖) («hu¹» : ∀ z u, ‖«Δ_u¹» z u‖ ≤ ‖u‖)
    («hz²» : ∀ z, ‖«Δ_z²» z‖ ≤ ‖z‖) («hu²» : ∀ z u, ‖«Δ_u²» z u‖ ≤ ‖u‖) :
    ReductionGuarantees
      (nonlinearResponse N (1 : Mat q q) «Δ_z¹» «Δ_u¹»)
      (nonlinearResponse (N.reduced W_r V_r) V_r «Δ_z²» «Δ_u²»)
      (fun z => drivenUpdate N (1 : Mat q q) «Δ_z¹» «Δ_u¹» z 0)
      (fun z => drivenUpdate (N.reduced W_r V_r) V_r «Δ_z²» «Δ_u²» z 0)
      (R.B_r N W_r V_r) := by
  have h := (R.B_r_finite_iff N W_r V_r).1 hfinite
  rcases h with ⟨hA,hA_hat,hV,hfull,hred,hnom⟩
  rw [R.B_r_eq_of_valid N W_r V_r ⟨hA,hA_hat,hV,hfull,hred,hnom⟩]
  exact uniform_nonlinear_comparison N W_r V_r hV hA hA_hat R.full.bounds R.reduced.bounds
    (R.full.valid_bounds N (1 : Mat q q) hfull) (R.reduced.valid_bounds (N.reduced W_r V_r) V_r hred)
    R.nominal.g hnom.1
    (nominal_error_storage_bound N.A (N.reduced W_r V_r).A N.B_u (N.reduced W_r V_r).B_u
      N.C (N.reduced W_r V_r).C R.nominal.X R.nominal.g hnom.1 hnom.2.1 hnom.2.2)
    «Δ_z¹» «Δ_z²» «Δ_u¹» «Δ_u²» «hz¹» «hu¹» «hz²» «hu²»

end
end Populus.ModelReduction.Certified
