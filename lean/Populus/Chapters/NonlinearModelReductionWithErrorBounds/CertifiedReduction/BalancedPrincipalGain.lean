import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.DiagonalSteinStorage

/-! Finite-prefix and infinite-energy error bounds for one balanced truncation. -/
namespace Populus.ModelReduction.Certified
open scoped BigOperators ENNReal
noncomputable section
variable {a b m p : ℕ}

@[simp] theorem balancedEnergy_zero (σ : Fin a → ℝ) (τ : ℝ) :
    balancedEnergy (b:=b) σ τ 0=0 := by
  have hd : drop (0 : Rn (a+b))=(0 : Rn b) := by ext i; rfl
  simp [balancedEnergy,hd]

theorem balancedEnergy_nonneg (σ : Fin a → ℝ) (τ : ℝ)
    (hσ : ∀ i,0≤σ i) (hτ : 0≤τ) (x : Rn (a+b)) :
    0≤balancedEnergy σ τ x := by
  exact add_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hσ i) (sq_nonneg _)))
    (mul_nonneg hτ (sq_nonneg _))

theorem balancedErrorStorage_nonneg (σ : Fin a → ℝ) (τ : ℝ)
    (hσ : ∀ i,0≤σ i) (hτ : 0≤τ) (x : Rn (a+b)) (xr : Rn a) :
    0≤balancedErrorStorage σ τ x xr := by
  exact add_nonneg (balancedEnergy_nonneg σ τ hσ hτ _)
    (mul_nonneg (sq_nonneg _) (balancedEnergy_nonneg _ _
      (fun i => inv_nonneg.2 (hσ i)) (inv_nonneg.2 hτ) _))

def balancedPrincipalResponse (A : Mat (a+b) (a+b)) (B : Mat (a+b) m)
    (u : ℕ → Rn m) : ℕ → Rn a :=
  rollout (fun xr v => take (act A (join xr (0 : Rn b))+act B v)) 0 u

theorem balanced_principal_prefix (σ : Fin a → ℝ) (τ : ℝ)
    (hσ : ∀ i,0≤σ i) (hτ : 0<τ)
    (A : Mat (a+b) (a+b)) (B : Mat (a+b) m) (C : Mat p (a+b))
    (hobs : ∀ z,balancedEnergy σ τ (act A z)+‖act C z‖^2≤balancedEnergy σ τ z)
    (hctrl : ∀ z u,balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ (act A z+act B u)≤
      balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ z+‖u‖^2)
    (u : ℕ → Rn m) (K : ℕ) :
    prefixEnergy (fun k => act C (linearResponse A B u k-
      join (balancedPrincipalResponse (b:=b) A B u k) (0 : Rn b))) K≤
        (2*τ)^2*prefixEnergy u K := by
  let x := linearResponse A B u
  let xr := balancedPrincipalResponse (b:=b) A B u
  let e := fun k => act C (x k-join (xr k) (0 : Rn b))
  have hs (k : ℕ) : balancedErrorStorage σ τ (x (k+1)) (xr (k+1))+‖e k‖^2≤
      balancedErrorStorage σ τ (x k) (xr k)+4*τ^2*‖u k‖^2 :=
    balanced_principal_one_step σ τ hτ A B C hobs hctrl (x k) (xr k) (u k)
  have ht (N : ℕ) : balancedErrorStorage σ τ (x N) (xr N)+
      (∑ k ∈ Finset.range N,‖e k‖^2)≤4*τ^2*(∑ k ∈ Finset.range N,‖u k‖^2) := by
    induction N with
    | zero =>
      have hj : join (0 : Rn a) (0 : Rn b)=0 := by
        ext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [join]
      simp [x,xr,linearResponse,balancedPrincipalResponse,rollout,
        balancedErrorStorage,hj]
    | succ N ih =>
      rw [Finset.sum_range_succ,Finset.sum_range_succ]
      linarith [hs N]
  have hf := ht (K+1)
  have hn := balancedErrorStorage_nonneg σ τ hσ (le_of_lt hτ) (x (K+1)) (xr (K+1))
  change prefixEnergy e K≤(2*τ)^2*prefixEnergy u K
  dsimp [prefixEnergy]
  nlinarith

theorem balanced_principal_induced_gain (σ : Fin a → ℝ) (τ : ℝ)
    (hσ : ∀ i,0≤σ i) (hτ : 0<τ)
    (A : Mat (a+b) (a+b)) (B : Mat (a+b) m) (C : Mat p (a+b))
    (hobs : ∀ z,balancedEnergy σ τ (act A z)+‖act C z‖^2≤balancedEnergy σ τ z)
    (hctrl : ∀ z u,balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ (act A z+act B u)≤
      balancedEnergy (fun i => (σ i)⁻¹) τ⁻¹ z+‖u‖^2) :
    inducedGain (fun u k => act C (linearResponse A B u k-
      join (balancedPrincipalResponse (b:=b) A B u k) (0 : Rn b)))≤ENNReal.ofReal (2*τ) := by
  have hc : 0≤2*τ := by positivity
  have hp (u : ℕ → Rn m) (K : ℕ) := balanced_principal_prefix σ τ hσ hτ A B C hobs hctrl u K
  unfold inducedGain
  refine iSup_le (fun u => iSup_le (fun hu => iSup_le (fun hne => ?_)))
  apply (ENNReal.div_le_iff (by simpa [ℓ₂_eq_zero_iff] using hne)
    ((finiteEnergy_iff_ℓ₂_ne_top u).1 hu)).2
  apply ℓ₂_le_of_prefix_bound _ u (2*τ) hc
  intro K
  have hs := Real.sqrt_le_sqrt (hp u K)
  simpa only [prefixNorm,Real.sqrt_mul (sq_nonneg (2*τ)),Real.sqrt_sq hc] using hs

end
end Populus.ModelReduction.Certified
