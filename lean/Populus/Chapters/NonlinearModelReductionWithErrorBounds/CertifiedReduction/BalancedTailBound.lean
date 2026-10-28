import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.RetainedMatrices

/-! Summing actual successive principal reductions gives the Hankel tail bound. -/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 800000

theorem weights_last_split {n : ℕ} (σ : Fin (n+1) → ℝ) :
    σ=Fin.addCases (fun i : Fin n => σ (Fin.castSucc i))
      (fun _ : Fin 1 => σ (Fin.last n)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp
    rfl
  · have hj : j=0 := Subsingleton.elim _ _
    subst j
    simp only [Fin.addCases_right]
    rfl

theorem weights_last_inverse {n : ℕ} (σ : Fin (n+1) → ℝ) :
    (fun i => (σ i)⁻¹)=Fin.addCases (fun i : Fin n => (σ (Fin.castSucc i))⁻¹)
      (fun _ : Fin 1 => (σ (Fin.last n))⁻¹) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp
    rfl
  · have hj : j=0 := Subsingleton.elim _ _
    subst j
    simp only [Fin.addCases_right]
    rfl

theorem balanced_tail_prefix {r k m p : ℕ} (σ : Fin (r+k) → ℝ)
    (hσ : ∀ i,0<σ i) (A : Mat (r+k) (r+k)) (B : Mat (r+k) m) (C : Mat p (r+k))
    (hobs : ∀ z,diagonalEnergy σ (act A z)+‖act C z‖^2≤diagonalEnergy σ z)
    (hctrl : ∀ z u,diagonalEnergy (fun i => (σ i)⁻¹) (act A z+act B u)≤
      diagonalEnergy (fun i => (σ i)⁻¹) z+‖u‖^2)
    (u : ℕ → Rn m) (K : ℕ) :
    prefixNorm (fun j => nominalOutput A B C u j-
      nominalOutput (retainedA A (Nat.le_add_right r k))
        (retainedB B (Nat.le_add_right r k)) (retainedC C (Nat.le_add_right r k)) u j) K≤
      2*tailSum σ*prefixNorm u K := by
  induction k with
  | zero => simp [nominalOutput,prefixNorm,prefixEnergy,tailSum]
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
      have h := hctrl z v
      have he (w : Rn ((r+k)+1)) : diagonalEnergy (fun i => (σ i)⁻¹) w=
          balancedEnergy (b:=1) (fun i => (σ' i)⁻¹) τ⁻¹ w := by
        exact (congrArg (fun f : Fin ((r+k)+1) → ℝ => diagonalEnergy f w)
          (weights_last_inverse (n:=r+k) σ)).trans (diagonalEnergy_balanced _ _ w)
      rw [he,he] at h
      exact h
    have hp₁ := balanced_principal_prefix (b:=1) σ' τ (fun i => le_of_lt (hσ' i)) hτ A B C hob hct u K
    rw [principal_output_difference (a:=r+k) (b:=1) A B C u] at hp₁
    have hn₁ : prefixNorm (fun j => nominalOutput A B C u j-
        nominalOutput (principalA (a:=r+k) (b:=1) A) (principalB (a:=r+k) (b:=1) B) (principalC (a:=r+k) (b:=1) C) u j) K≤
          2*τ*prefixNorm u K := by
      have hs := Real.sqrt_le_sqrt hp₁
      simpa only [prefixNorm,Real.sqrt_mul (sq_nonneg (2*τ)),Real.sqrt_sq (by positivity : 0≤2*τ)] using hs
    have hn₂ := ih σ' hσ' (principalA (a:=r+k) (b:=1) A) (principalB (a:=r+k) (b:=1) B) (principalC (a:=r+k) (b:=1) C)
      (principal_observability_storage (a:=r+k) (b:=1) (p:=p) σ' τ (le_of_lt hτ) A C hob)
      (principal_controllability_storage (a:=r+k) (b:=1) (m:=m) σ' τ (le_of_lt hτ) A B hct)
    simp only [principalA_eq_retained,principalB_eq_retained,principalC_eq_retained,
      retainedA_trans,retainedB_trans,retainedC_trans] at hn₂
    have ht := prefixNorm_add_le
      (fun j => nominalOutput A B C u j-
        nominalOutput (principalA (a:=r+k) (b:=1) A) (principalB (a:=r+k) (b:=1) B) (principalC (a:=r+k) (b:=1) C) u j)
      (fun j => nominalOutput (principalA (a:=r+k) (b:=1) A) (principalB (a:=r+k) (b:=1) B) (principalC (a:=r+k) (b:=1) C) u j-
        nominalOutput (retainedA A (Nat.le_add_right r (k+1)))
          (retainedB B (Nat.le_add_right r (k+1))) (retainedC C (Nat.le_add_right r (k+1))) u j) K
    have he : (fun j => (nominalOutput A B C u j-
          nominalOutput (principalA (a:=r+k) (b:=1) A) (principalB (a:=r+k) (b:=1) B) (principalC (a:=r+k) (b:=1) C) u j)+
        (nominalOutput (principalA (a:=r+k) (b:=1) A) (principalB (a:=r+k) (b:=1) B) (principalC (a:=r+k) (b:=1) C) u j-
          nominalOutput (retainedA A (Nat.le_add_right r (k+1)))
            (retainedB B (Nat.le_add_right r (k+1))) (retainedC C (Nat.le_add_right r (k+1))) u j))=
      (fun j => nominalOutput A B C u j-
        nominalOutput (retainedA A (Nat.le_add_right r (k+1)))
          (retainedB B (Nat.le_add_right r (k+1))) (retainedC C (Nat.le_add_right r (k+1))) u j) := by
      funext j
      abel
    rw [he] at ht
    calc
      _ ≤ _ := ht
      _ ≤ 2*τ*prefixNorm u K+2*tailSum σ'*prefixNorm u K := by
        apply add_le_add hn₁
        simpa only [principalA_eq_retained,principalB_eq_retained,principalC_eq_retained] using hn₂
      _ = _ := by rw [tailSum_succ]; dsimp [σ',τ]; ring

theorem balanced_tail_induced_gain {r k m p : ℕ} (σ : Fin (r+k) → ℝ)
    (hσ : ∀ i,0<σ i) (A : Mat (r+k) (r+k)) (B : Mat (r+k) m) (C : Mat p (r+k))
    (hobs : ∀ z,diagonalEnergy σ (act A z)+‖act C z‖^2≤diagonalEnergy σ z)
    (hctrl : ∀ z u,diagonalEnergy (fun i => (σ i)⁻¹) (act A z+act B u)≤
      diagonalEnergy (fun i => (σ i)⁻¹) z+‖u‖^2) :
    inducedGain (fun u j => nominalOutput A B C u j-
      nominalOutput (retainedA A (Nat.le_add_right r k))
        (retainedB B (Nat.le_add_right r k)) (retainedC C (Nat.le_add_right r k)) u j)≤
      ENNReal.ofReal (2*tailSum σ) := by
  have hc : 0≤2*tailSum σ := mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun i _ => le_of_lt (hσ _)))
  unfold inducedGain
  refine iSup_le (fun u => iSup_le (fun hu => iSup_le (fun hne => ?_)))
  apply (ENNReal.div_le_iff (by simpa [ℓ₂_eq_zero_iff] using hne)
    ((finiteEnergy_iff_ℓ₂_ne_top u).1 hu)).2
  exact ℓ₂_le_of_prefix_bound _ u _ hc (balanced_tail_prefix σ hσ A B C hobs hctrl u)

theorem balanced_tail_from_stein {r k m p : ℕ} (σ : Fin (r+k) → ℝ)
    (hσ : ∀ i,0<σ i) (A : Mat (r+k) (r+k)) (B : Mat (r+k) m) (C : Mat p (r+k))
    (hP : (Matrix.diagonal σ-A*Matrix.diagonal σ*A.transpose-B*B.transpose).PosSemidef)
    (hQ : (Matrix.diagonal σ-A.transpose*Matrix.diagonal σ*A-C.transpose*C).PosSemidef) :
    inducedGain (fun u j => nominalOutput A B C u j-
      nominalOutput (retainedA A (Nat.le_add_right r k))
        (retainedB B (Nat.le_add_right r k)) (retainedC C (Nat.le_add_right r k)) u j)≤
      ENNReal.ofReal (2*tailSum σ) :=
  balanced_tail_induced_gain σ hσ A B C (observability_stein_storage σ A C hQ)
    (controllability_stein_storage σ hσ A B hP)

end
end Populus.ModelReduction.Certified
