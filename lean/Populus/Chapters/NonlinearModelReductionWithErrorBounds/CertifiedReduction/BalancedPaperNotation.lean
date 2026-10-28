import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.BalancedTruncation

/-!
# Paper-facing balanced-truncation notation

Finite coordinates are zero based: paper σ_i is σ ⟨i-1,...⟩. Here q=r+k,
R in the intermediate algebra is exactly T⁻¹, and all three augmented input
ports retain their own Euclidean dimensions. Ordered/separated singular
values and positive Stein Gramians are retained in this paper-facing wrapper.
-/
namespace Populus.ModelReduction.Certified.PaperBalancing
open scoped ENNReal
noncomputable section
variable {q r m p_u p_z : ℕ}

def B_aug (B_u : Mat q m) (B_δu : Mat q p_u) (B_δz : Mat q p_z) :=
  inputJoin B_u (inputJoin B_δu B_δz)
def W_r (T : Mat q q) (h : r≤q) : Mat r q := balancedW T h
def V_r (T : Mat q q) (h : r≤q) : Mat q r := balancedV T⁻¹ h
def «b_r⁰» {r k : ℕ} (σ : Fin (r+k) → ℝ) : ℝ := 2*tailSum σ

/-- **Paper `def:balanced`, `eq:balanced-nominal-upper`.** This wrapper keeps
the paper's hypotheses, indexing and projection symbols literally visible. -/
theorem balanced_nominal_stability_and_error {r k m p p_u p_z : ℕ}
    (hr : 0<r) (hk : 0<k) (σ : Fin (r+k) → ℝ)
    (hσ : ∀ i,0<σ i) (_horder : Antitone σ)
    (_hgap : σ ⟨r,by omega⟩<σ ⟨r-1,by omega⟩)
    (A : Mat (r+k) (r+k)) (B_u : Mat (r+k) m)
    (B_δu : Mat (r+k) p_u) (B_δz : Mat (r+k) p_z) (C : Mat p (r+k))
    (P Q T : Mat (r+k) (r+k)) (_hPpos : P.PosDef) (_hQpos : Q.PosDef)
    (hA : Schur A) (hT : IsUnit T)
    (hP : P=A*P*A.transpose+B_aug B_u B_δu B_δz*(B_aug B_u B_δu B_δz).transpose)
    (hQ : Q=A.transpose*Q*A+C.transpose*C)
    (hbalancedP : Matrix.diagonal σ=T*P*T.transpose)
    (hbalancedQ : Matrix.diagonal σ=T⁻¹.transpose*Q*T⁻¹) :
    W_r T (Nat.le_add_right r k)*V_r T (Nat.le_add_right r k)=1 ∧
      Schur (W_r T (Nat.le_add_right r k)*A*V_r T (Nat.le_add_right r k)) ∧
      inducedGain (fun u j => nominalOutput A B_u C u j-
        nominalOutput
          (W_r T (Nat.le_add_right r k)*A*V_r T (Nat.le_add_right r k))
          (W_r T (Nat.le_add_right r k)*B_u)
          (C*V_r T (Nat.le_add_right r k)) u j)≤ENNReal.ofReal («b_r⁰» σ) := by
  exact balanced_truncation_specialization σ hσ A B_u (inputJoin B_δu B_δz) C P Q T T⁻¹ hA
    (Matrix.mul_nonsing_inv T ((Matrix.isUnit_iff_isUnit_det T).mp hT))
    (Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp hT)) hP hQ hbalancedP hbalancedQ

end
end Populus.ModelReduction.Certified.PaperBalancing
