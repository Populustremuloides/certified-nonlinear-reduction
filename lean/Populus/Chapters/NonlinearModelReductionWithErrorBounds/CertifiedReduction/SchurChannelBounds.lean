import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ChannelGains

/-!
# Schur stability implies finite nominal channel gains

This file closes the finite-gain premise used implicitly by the paper's channel
definitions. A genuine free-trajectory energy supplies a storage function;
Young's inequality and telescoping then bound every actual nominal response.
No bounded-real converse, gain oracle, or desired state-energy bound is assumed.
-/
namespace Populus.ModelReduction.Certified
open scoped BigOperators Matrix.Norms.L2Operator ENNReal
noncomputable section
variable {n m p : ℕ}

theorem freeResponse_eq_iterate (A : Mat n n) (z : Rn n) :
    freeResponse A z = fun k => (act A)^[k] z := by
  funext k
  induction k with
  | zero => simp
  | succ k ih => simpa [Function.iterate_succ_apply'] using congrArg (act A) ih

/-- The actual summed nominal free-response energy. -/
def V_A (A : Mat n n) (z : Rn n) : ℝ := energy (freeResponse A z)

@[simp] theorem V_A_zero (A : Mat n n) : V_A A 0=0 := by simp [V_A,energy]

theorem V_A_nonneg (A : Mat n n) (z : Rn n) : 0 ≤ V_A A z :=
  tsum_nonneg (fun k => sq_nonneg _)

private theorem energy_of_prefixNorm_bound {E : Type*} [NormedAddCommGroup E]
    (z : ℕ → E) (C : ℝ) (hC : 0 ≤ C) (h : ∀ K, prefixNorm z K ≤ C) :
    FiniteEnergy z ∧ energy z ≤ C^2 := by
  have hp (K : ℕ) : prefixEnergy z K ≤ C^2 := by
    have hs := Real.sq_sqrt (prefixEnergy_nonneg z K)
    have hn := prefixNorm_nonneg z K
    have hb := h K
    dsimp [prefixNorm] at hn hb
    nlinarith
  exact ⟨finiteEnergy_of_prefix_bound z _ (sq_nonneg _) hp,
    energy_le_of_prefix_bound z _ (sq_nonneg _) hp⟩

private theorem free_energy_bounds (A : Mat n n) (c : ℝ) (hc : 1 ≤ c)
    (hfree : ∀ z K, prefixNorm (freeResponse A z) K ≤ c*‖z‖) :
    ∀ z, FiniteEnergy (freeResponse A z) ∧ V_A A z ≤ c^2*‖z‖^2 := by
  intro z
  have h := energy_of_prefixNorm_bound (freeResponse A z) (c*‖z‖)
    (mul_nonneg (by linarith) (norm_nonneg _)) (hfree z)
  exact ⟨h.1,by simpa [V_A,mul_pow] using h.2⟩

private theorem V_A_shift (A : Mat n n) (z : Rn n)
    (hz : FiniteEnergy (freeResponse A z)) : V_A A (act A z)=V_A A z-‖z‖^2 := by
  simpa [Υ,V_A,freeResponse_eq_iterate] using
    Υ_update (act A) z (by simpa [freeResponse_eq_iterate] using hz)

private theorem V_A_triangle (A : Mat n n) (x y : Rn n)
    (hx : FiniteEnergy (freeResponse A x)) (hy : FiniteEnergy (freeResponse A y)) :
    V_A A (x+y) ≤ (Real.sqrt (V_A A x)+Real.sqrt (V_A A y))^2 := by
  have heq : freeResponse A (x+y)=fun k => freeResponse A x k+freeResponse A y k := by
    funext k
    simp [freeResponse]
  have hp (K : ℕ) : prefixNorm (freeResponse A (x+y)) K ≤
      Real.sqrt (V_A A x)+Real.sqrt (V_A A y) := by
    rw [heq]
    exact (prefixNorm_add_le _ _ K).trans (add_le_add
      (Real.sqrt_le_sqrt (prefixEnergy_le_energy _ hx K))
      (Real.sqrt_le_sqrt (prefixEnergy_le_energy _ hy K)))
  exact (energy_of_prefixNorm_bound _ _ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hp).2

/-- A concrete storage inequality obtained from actual Schur free responses. -/
theorem schur_storage_step (A : Mat n n) (B : Mat n m) (c : ℝ) (hc : 1 ≤ c)
    (hfree : ∀ z K, prefixNorm (freeResponse A z) K ≤ c*‖z‖)
    (z : Rn n) (u : Rn m) :
    V_A A (act A z+act B u)+(1/2:ℝ)*‖z‖^2 ≤
      V_A A z+(2*c^4+c^2)*‖B‖^2*‖u‖^2 := by
  have hf := free_energy_bounds A c hc hfree
  have hshift := V_A_shift A z (hf z).1
  have ht := V_A_triangle A (act A z) (act B u) (hf _).1 (hf _).1
  have hB : ‖act B u‖ ≤ ‖B‖*‖u‖ := Matrix.l2_opNorm_mulVec B u
  have hrootA : Real.sqrt (V_A A (act A z)) ≤ c*‖z‖ := by
    have hs := (hf z).2
    have hsq := Real.sq_sqrt (V_A_nonneg A (act A z))
    have hn := Real.sqrt_nonneg (V_A A (act A z))
    have hc0 : 0 ≤ c := by linarith
    apply (sq_le_sq₀ hn (mul_nonneg hc0 (norm_nonneg z))).1
    nlinarith [sq_nonneg ‖z‖]
  have hrootB : Real.sqrt (V_A A (act B u)) ≤ c*‖B‖*‖u‖ := by
    have hs := (hf (act B u)).2
    have hsq := Real.sq_sqrt (V_A_nonneg A (act B u))
    have hn := Real.sqrt_nonneg (V_A A (act B u))
    have hb2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hB
    have hbound := mul_le_mul_of_nonneg_left hb2 (sq_nonneg c)
    have hc0 : 0 ≤ c := by linarith
    apply (sq_le_sq₀ hn (mul_nonneg (mul_nonneg hc0 (norm_nonneg B)) (norm_nonneg u))).1
    nlinarith
  have hcross : Real.sqrt (V_A A (act A z))*Real.sqrt (V_A A (act B u)) ≤
      (c*‖z‖)*(c*‖B‖*‖u‖) :=
    mul_le_mul hrootA hrootB (Real.sqrt_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))
  have hyoung : 2*(c*‖z‖)*(c*‖B‖*‖u‖) ≤
      (1/2:ℝ)*‖z‖^2+2*c^4*‖B‖^2*‖u‖^2 := by
    nlinarith [sq_nonneg (‖z‖-2*c^2*‖B‖*‖u‖)]
  have hVB : V_A A (act B u) ≤ c^2*‖B‖^2*‖u‖^2 := by
    have hs := (hf (act B u)).2
    have hb2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hB
    have hbound := mul_le_mul_of_nonneg_left hb2 (sq_nonneg c)
    nlinarith
  have hsA := Real.sq_sqrt (V_A_nonneg A (act A z))
  have hsB := Real.sq_sqrt (V_A_nonneg A (act B u))
  nlinarith

/-- Every Schur nominal realization has a genuine finite induced channel gain.
This justifies treating the channel gains as finite real constants in the paper. -/
theorem schur_channel_gain_finite {n : ℕ} [NeZero n]
    (A : Mat n n) (B : Mat n m) (O : Mat p n) (hA : Schur A) :
    channelGain A B O ≠ ⊤ := by
  obtain ⟨c,hc,hfree⟩ := schur_free_response_bound A hA
  let D : ℝ := (2*c^4+c^2)*‖B‖^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hstate (w : ℕ → Rn m) (K : ℕ) :
      prefixEnergy (linearResponse A B w) K ≤ (2*D)*prefixEnergy w K := by
    have ht (N : ℕ) : V_A A (linearResponse A B w N)+
        (1/2:ℝ)*(∑ k ∈ Finset.range N, ‖linearResponse A B w k‖^2) ≤
        D*(∑ k ∈ Finset.range N, ‖w k‖^2) := by
      induction N with
      | zero => simp [linearResponse,rollout]
      | succ N ih =>
        have hs := schur_storage_step A B c hc hfree (linearResponse A B w N) (w N)
        change V_A A (linearResponse A B w (N+1))+(1/2:ℝ)*‖linearResponse A B w N‖^2 ≤
          V_A A (linearResponse A B w N)+D*‖w N‖^2 at hs
        rw [Finset.sum_range_succ,Finset.sum_range_succ]
        nlinarith
    have hp := ht (K+1)
    change _ ≤ (2*D)*(∑ k ∈ Finset.range (K+1), ‖w k‖^2)
    dsimp [prefixEnergy]
    linarith [V_A_nonneg A (linearResponse A B w (K+1))]
  let g : ℝ := ‖O‖*Real.sqrt (2*D)
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hprefix : HasPrefixChannelGain A B O g := by
    refine ⟨hg,fun w K => ?_⟩
    have hs := Real.sqrt_le_sqrt (hstate w K)
    have hsp : prefixNorm (linearResponse A B w) K ≤ Real.sqrt (2*D)*prefixNorm w K := by
      simpa [prefixNorm,Real.sqrt_mul (by positivity : 0 ≤ 2*D)] using hs
    calc
      _ ≤ ‖O‖*prefixNorm (linearResponse A B w) K :=
        prefixNorm_mul_bound _ _ ‖O‖ (norm_nonneg _) (fun k => Matrix.l2_opNorm_mulVec O _) K
      _ ≤ ‖O‖*(Real.sqrt (2*D)*prefixNorm w K) := mul_le_mul_of_nonneg_left hsp (norm_nonneg _)
      _ = g*prefixNorm w K := by dsimp [g]; ring
  have hle := (prefix_channel_gain_iff_induced_gain_bound A B O g hg).1 hprefix
  exact ne_of_lt (hle.trans_lt ENNReal.ofReal_lt_top)

/-- The paper's exact gain, converted to a real only after proving finiteness,
satisfies the finite-prefix bound used in the nonlinear proof. -/
theorem exact_channel_gain_prefix {n : ℕ} [NeZero n]
    (A : Mat n n) (B : Mat n m) (O : Mat p n) (hA : Schur A) :
    HasPrefixChannelGain A B O (channelGain A B O).toReal := by
  apply (prefix_channel_gain_iff_induced_gain_bound A B O _ ENNReal.toReal_nonneg).2
  rw [ENNReal.ofReal_toReal (schur_channel_gain_finite A B O hA)]

end
end Populus.ModelReduction.Certified
