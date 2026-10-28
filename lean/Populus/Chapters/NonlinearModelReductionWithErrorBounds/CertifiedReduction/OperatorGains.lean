import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ChannelGains

/-!
# Extended signal norms and actual nonlinear induced gains

All output norms are extended before summability has been established. The
supremum in `inducedGain` is over actual nonzero finite-energy applied inputs.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {E F H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup H]

theorem ℓ₂_le_of_prefix_bound (z : ℕ → E) (u : ℕ → F) (g : ℝ) (hg : 0 ≤ g)
    (h : ∀ K, prefixNorm z K ≤ g*prefixNorm u K) :
    ℓ₂ z ≤ ENNReal.ofReal g*ℓ₂ u := by
  apply iSup_le
  intro K
  have hp := ENNReal.ofReal_le_ofReal (h K)
  rw [ENNReal.ofReal_mul hg] at hp
  exact hp.trans (mul_le_mul_left' (le_iSup (fun N => ENNReal.ofReal (prefixNorm u N)) K) _)

theorem ℓ₂_add_le (z w : ℕ → E) : ℓ₂ (fun k => z k+w k) ≤ ℓ₂ z+ℓ₂ w := by
  apply iSup_le
  intro K
  calc
    _ ≤ ENNReal.ofReal (prefixNorm z K+prefixNorm w K) :=
      ENNReal.ofReal_le_ofReal (prefixNorm_add_le z w K)
    _ = ENNReal.ofReal (prefixNorm z K)+ENNReal.ofReal (prefixNorm w K) :=
      ENNReal.ofReal_add (prefixNorm_nonneg z K) (prefixNorm_nonneg w K)
    _ ≤ _ := add_le_add (le_iSup (fun N => ENNReal.ofReal (prefixNorm z N)) K)
      (le_iSup (fun N => ENNReal.ofReal (prefixNorm w N)) K)

@[simp] theorem ℓ₂_zero : ℓ₂ (fun _ : ℕ => (0 : E))=0 := by
  simp [ℓ₂,prefixNorm,prefixEnergy]

@[simp] theorem ℓ₂_neg (z : ℕ → E) : ℓ₂ (fun k => -z k)=ℓ₂ z := by
  simp only [ℓ₂,prefixNorm,prefixEnergy,norm_neg]

/-- Induced gain of an actual response map, with no assumed output membership. -/
def inducedGain (G : (ℕ → E) → (ℕ → F)) : ℝ≥0∞ :=
  ⨆ u, ⨆ (_ : FiniteEnergy u), ⨆ (_ : u≠fun _ => 0), ℓ₂ (G u)/ℓ₂ u

@[simp] theorem inducedGain_neg (G : (ℕ → E) → (ℕ → F)) :
    inducedGain (fun u k => -G u k)=inducedGain G := by
  simp only [inducedGain,ℓ₂_neg]

/-- Supremum-of-ratios and the uniform signal inequality agree. -/
theorem inducedGain_le_iff (G : (ℕ → E) → (ℕ → F))
    (hzero : G (fun _ => 0)=fun _ => 0) (g : ℝ) (hg : 0 ≤ g) :
    inducedGain G ≤ ENNReal.ofReal g ↔
      ∀ u, FiniteEnergy u → ℓ₂ (G u) ≤ ENNReal.ofReal g*ℓ₂ u := by
  constructor
  · intro h u hu
    by_cases hne : u=fun _ => 0
    · subst u; simp [hzero]
    · apply (ENNReal.div_le_iff (by simpa [ℓ₂_eq_zero_iff] using hne)
        ((finiteEnergy_iff_ℓ₂_ne_top u).1 hu)).1
      exact (show ℓ₂ (G u)/ℓ₂ u ≤ inducedGain G from
        le_iSup_of_le u (le_iSup_of_le hu (le_iSup_of_le hne le_rfl))).trans h
  · intro h
    refine iSup_le (fun u => iSup_le (fun hu => iSup_le (fun hne => ?_)))
    exact (ENNReal.div_le_iff (by simpa [ℓ₂_eq_zero_iff] using hne)
      ((finiteEnergy_iff_ℓ₂_ne_top u).1 hu)).2 (h u hu)

/-- A finite gain bound proves actual output summability. -/
theorem finiteEnergy_of_gain_bound (z : ℕ → F) (u : ℕ → E) (hu : FiniteEnergy u)
    (g : ℝ) (h : ℓ₂ z ≤ ENNReal.ofReal g*ℓ₂ u) : FiniteEnergy z := by
  apply (finiteEnergy_iff_ℓ₂_ne_top z).2
  exact ne_of_lt (h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.2 ((finiteEnergy_iff_ℓ₂_ne_top u).1 hu))))

/-- Triangle comparison of actual response maps, including their zero-input
behavior. This is used for nonlinear/nominal departure decompositions. -/
theorem inducedGain_add_bound (G H : (ℕ → E) → (ℕ → F))
    (hG0 : G (fun _ => 0)=fun _ => 0) (hH0 : H (fun _ => 0)=fun _ => 0)
    (g h : ℝ) (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hG : inducedGain G ≤ ENNReal.ofReal g) (hH : inducedGain H ≤ ENNReal.ofReal h) :
    inducedGain (fun u k => G u k+H u k) ≤ ENNReal.ofReal (g+h) := by
  apply (inducedGain_le_iff _ (by simp [hG0,hH0]) _ (add_nonneg hg hh)).2
  intro u hu
  calc
    _ ≤ ℓ₂ (G u)+ℓ₂ (H u) := ℓ₂_add_le _ _
    _ ≤ ENNReal.ofReal g*ℓ₂ u+ENNReal.ofReal h*ℓ₂ u :=
      add_le_add ((inducedGain_le_iff G hG0 g hg).1 hG u hu)
        ((inducedGain_le_iff H hH0 h hh).1 hH u hu)
    _ = ENNReal.ofReal (g+h)*ℓ₂ u := by rw [ENNReal.ofReal_add hg hh,add_mul]

/-- Three-term comparison used for independently chosen envelope-bounded
nonlinear updates. No common residual operator is required. -/
theorem inducedGain_three_term_comparison
    (G G₀ H H₀ : (ℕ → E) → (ℕ → F))
    (hG : G (fun _ => 0)=fun _ => 0) (hG₀ : G₀ (fun _ => 0)=fun _ => 0)
    (hH : H (fun _ => 0)=fun _ => 0) (hH₀ : H₀ (fun _ => 0)=fun _ => 0)
    (ε b ε_hat : ℝ) (hε : 0≤ε) (hb : 0≤b) (hε_hat : 0≤ε_hat)
    (hdep : inducedGain (fun u k => G u k-G₀ u k) ≤ ENNReal.ofReal ε)
    (hnom : inducedGain (fun u k => G₀ u k-H₀ u k) ≤ ENNReal.ofReal b)
    (hdep_hat : inducedGain (fun u k => H u k-H₀ u k) ≤ ENNReal.ofReal ε_hat) :
    inducedGain (fun u k => G u k-H u k) ≤ ENNReal.ofReal (ε+b+ε_hat) := by
  have h₁ := inducedGain_add_bound (fun u k => G u k-G₀ u k) (fun u k => G₀ u k-H₀ u k)
    (by simp [hG,hG₀]) (by simp [hG₀,hH₀]) ε b hε hb hdep hnom
  have h₂ : inducedGain (fun u k => -(H u k-H₀ u k)) ≤ ENNReal.ofReal ε_hat := by
    simpa only [inducedGain_neg] using hdep_hat
  have h₃ := inducedGain_add_bound
    (fun u k => (G u k-G₀ u k)+(G₀ u k-H₀ u k)) (fun u k => -(H u k-H₀ u k))
    (by simp [hG,hG₀,hH₀]) (by simp [hH,hH₀]) (ε+b) ε_hat (add_nonneg hε hb) hε_hat h₁ h₂
  have heq : (fun u k => (G u k-G₀ u k+(G₀ u k-H₀ u k))+ -(H u k-H₀ u k))=
      (fun u k => G u k-H u k) := by funext u k; abel
  rwa [heq] at h₃

end
end Populus.ModelReduction.Certified
