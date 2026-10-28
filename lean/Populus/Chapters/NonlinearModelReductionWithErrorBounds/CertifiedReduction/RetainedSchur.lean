import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.BalancedTailBound

/-! Schur stability of every retained principal nominal realization. -/
namespace Populus.ModelReduction.Certified
noncomputable section
set_option maxHeartbeats 800000

theorem balanced_retained_schur {r k m p : ℕ} (σ : Fin (r+k) → ℝ)
    (hσ : ∀ i,0<σ i) (A : Mat (r+k) (r+k)) (B : Mat (r+k) m) (C : Mat p (r+k))
    (hA : Schur A)
    (hobs : ∀ z,diagonalEnergy σ (act A z)+‖act C z‖^2≤diagonalEnergy σ z)
    (hctrl : ∀ z u,diagonalEnergy (fun i => (σ i)⁻¹) (act A z+act B u)≤
      diagonalEnergy (fun i => (σ i)⁻¹) z+‖u‖^2) :
    Schur (retainedA A (Nat.le_add_right r k)) := by
  induction k with
  | zero => simpa using hA
  | succ k ih =>
    let σ' : Fin (r+k) → ℝ := fun i => σ (Fin.castSucc i)
    let τ := σ (Fin.last (r+k))
    have hτ : 0<τ := hσ _
    have hσ' : ∀ i,0<σ' i := fun i => hσ _
    have hob (z : Rn ((r+k)+1)) : balancedEnergy (b:=1) σ' τ (act A z)+‖act C z‖^2≤balancedEnergy (b:=1) σ' τ z := by
      have h := hobs z
      rw [weights_last_split (n:=r+k) σ,diagonalEnergy_balanced,diagonalEnergy_balanced] at h
      exact h
    have hct (z : Rn ((r+k)+1)) (v : Rn m) :
        balancedEnergy (b:=1) (fun i => (σ' i)⁻¹) τ⁻¹ (act A z+act B v)≤
          balancedEnergy (b:=1) (fun i => (σ' i)⁻¹) τ⁻¹ z+‖v‖^2 := by
      have he (w : Rn ((r+k)+1)) : diagonalEnergy (fun i => (σ i)⁻¹) w=
          balancedEnergy (b:=1) (fun i => (σ' i)⁻¹) τ⁻¹ w := by
        exact (congrArg (fun f : Fin ((r+k)+1) → ℝ => diagonalEnergy f w)
          (weights_last_inverse (n:=r+k) σ)).trans (diagonalEnergy_balanced _ _ w)
      simpa only [he] using hctrl z v
    have has := principal_schur_of_balanced_dissipation (a:=r+k) (b:=1) σ' τ hσ' hτ A hA
      (fun z => (le_add_of_nonneg_right (sq_nonneg ‖act C z‖)).trans (hob z))
    have hi := ih σ' hσ' (principalA (a:=r+k) (b:=1) A)
      (principalB (a:=r+k) (b:=1) B) (principalC (a:=r+k) (b:=1) C) has
      (principal_observability_storage (a:=r+k) (b:=1) (p:=p) σ' τ (le_of_lt hτ) A C hob)
      (principal_controllability_storage (a:=r+k) (b:=1) (m:=m) σ' τ (le_of_lt hτ) A B hct)
    simpa only [principalA_eq_retained,retainedA_trans] using hi

end
end Populus.ModelReduction.Certified
