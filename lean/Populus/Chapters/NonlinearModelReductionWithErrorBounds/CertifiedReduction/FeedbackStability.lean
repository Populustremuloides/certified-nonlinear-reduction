import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SchurChannelBounds

/-!
# Global exponential stability of the actual nonlinear feedback recurrence

Paper: the autonomous conclusions of `lem:departures` and its prescribed-
reconstruction corollary. The observed residual-driving state is `O z`.
Injectivity of `O`, not orthonormality or exact stored biorthogonality, suffices.
-/
namespace Populus.ModelReduction.Certified
open scoped Matrix.Norms.L2Operator
noncomputable section
variable {d q m p p_u p_z : ℕ}

/-- A finite-dimensional injective reconstruction has a global norm inverse
bound. This is a theorem about the actual linear map, not an added premise. -/
theorem reconstruction_inverse_bound (O : Mat q d) (hO : Function.Injective (act O)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ z, ‖z‖ ≤ κ*‖act O z‖ := by
  obtain ⟨κ,hκ,hanti⟩ := (Matrix.toEuclideanLin O).injective_iff_antilipschitz.mp hO
  refine ⟨κ,by exact_mod_cast hκ,fun z => ?_⟩
  simpa [act,dist_zero_right] using hanti.le_mul_dist z 0

/-- With zero applied input, the actual nonlinear trajectory is the free
nominal response plus the autonomous residual's nominal channel response. -/
theorem autonomous_decomposition
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖) (z₀ : Rn d) :
    let f := fun z => drivenUpdate N O Δ_z Δ_u z 0
    ∀ k, f^[k] z₀=freeResponse N.A z₀ k+
      linearResponse N.A N.B_δz (fun j => Δ_z (act O (f^[j] z₀))) k := by
  have hzero (z : Rn q) : Δ_u z 0=0 := norm_eq_zero.mp (le_antisymm
    (by simpa using hu z 0) (norm_nonneg _))
  have heq : rollout (drivenUpdate N O Δ_z Δ_u) z₀ (fun _ => 0)=
      fun k => (fun z => drivenUpdate N O Δ_z Δ_u z 0)^[k] z₀ := by
    funext k
    induction k with
    | zero => rfl
    | succ k ih =>
        simpa only [rollout,Function.iterate_succ_apply'] using
          (congrArg (fun z => drivenUpdate N O Δ_z Δ_u z 0) ih)
  dsimp only
  intro k
  have h := trajectory_decomposition N O Δ_z Δ_u z₀ (fun _ => 0) k
  simpa only [heq,hzero,linearResponse_zero,add_zero] using h

/-- Global exponential stability follows from Schur nominal dynamics, the
pointwise residual envelope, and a strict autonomous channel margin.
No derivative, incremental gain, or one-step Euclidean decrease is assumed. -/
theorem feedback_globally_exponentially_stable [NeZero d]
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (hA : Schur N.A) (hO : Function.Injective (act O))
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖)
    (g_δz : ℝ) (hg : HasPrefixChannelGain N.A N.B_δz O g_δz)
    (hsmall : g_δz<1) :
    GloballyExponentiallyStable (fun z => drivenUpdate N O Δ_z Δ_u z 0) := by
  obtain ⟨c,hc,hfree⟩ := schur_free_response_bound N.A hA
  obtain ⟨κ,hκ,hinverse⟩ := reconstruction_inverse_bound O hO
  let f := fun z => drivenUpdate N O Δ_z Δ_u z 0
  let L : ℝ := ‖O‖*c/(1-g_δz)
  have hden : 0 < 1-g_δz := by linarith
  have hL : 0 ≤ L := div_nonneg (mul_nonneg (norm_nonneg _) (by linarith)) hden.le
  have hprefix (z₀ : Rn d) (K : ℕ) :
      prefixNorm (fun k => act O (f^[k] z₀)) K ≤ L*‖z₀‖ := by
    let η := fun k => act O (f^[k] z₀)
    let δ := fun k => Δ_z (η k)
    have hdec : η=fun k => act O (freeResponse N.A z₀ k)+
        act O (linearResponse N.A N.B_δz δ k) := by
      funext k
      rw [show η k=act O (f^[k] z₀) from rfl,
        autonomous_decomposition N O Δ_z Δ_u hu z₀ k,act_add]
    have hfirst : prefixNorm (fun k => act O (freeResponse N.A z₀ k)) K ≤
        ‖O‖*c*‖z₀‖ := by
      calc
        _ ≤ ‖O‖*prefixNorm (freeResponse N.A z₀) K :=
          prefixNorm_mul_bound _ _ _ (norm_nonneg _) (fun k => Matrix.l2_opNorm_mulVec O _) K
        _ ≤ ‖O‖*(c*‖z₀‖) := mul_le_mul_of_nonneg_left (hfree z₀ K) (norm_nonneg _)
        _ = _ := by ring
    have hδ : prefixNorm δ K ≤ prefixNorm η K := prefixNorm_mono _ _ (fun k => hz _) K
    have hb : prefixNorm η K ≤ ‖O‖*c*‖z₀‖+g_δz*prefixNorm η K := by
      calc
        _ = prefixNorm (fun k => act O (freeResponse N.A z₀ k)+
            act O (linearResponse N.A N.B_δz δ k)) K := congrArg (fun s => prefixNorm s K) hdec
        _ ≤ _ := prefixNorm_add_le _ _ K
        _ ≤ ‖O‖*c*‖z₀‖+g_δz*prefixNorm δ K := add_le_add hfirst (hg.2 δ K)
        _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hδ hg.1) _
    change prefixNorm η K ≤ L*‖z₀‖
    dsimp [L]
    rw [div_mul_eq_mul_div,(le_div_iff₀ hden)]
    nlinarith
  have hstate (z₀ : Rn d) (K : ℕ) : prefixNorm (fun k => f^[k] z₀) K ≤ (κ*L)*‖z₀‖ := by
    calc
      _ ≤ κ*prefixNorm (fun k => act O (f^[k] z₀)) K :=
        prefixNorm_mul_bound _ _ κ hκ.le (fun k => hinverse _) K
      _ ≤ κ*(L*‖z₀‖) := mul_le_mul_of_nonneg_left (hprefix z₀ K) hκ.le
      _ = _ := by ring
  let M : ℝ := 1+(κ*L)^2
  apply globally_exponentially_stable_of_summed_energy f M (by dsimp [M]; linarith [sq_nonneg (κ*L)])
  intro z₀
  have henergy (K : ℕ) : prefixEnergy (fun k => f^[k] z₀) K ≤ (κ*L)^2*‖z₀‖^2 := by
    have hb := hstate z₀ K
    have hn := prefixNorm_nonneg (fun k => f^[k] z₀) K
    have hprod : 0 ≤ (κ*L)*‖z₀‖ := mul_nonneg (mul_nonneg hκ.le hL) (norm_nonneg _)
    have hs := (sq_le_sq₀ hn hprod).2 hb
    simpa only [prefixNorm,Real.sq_sqrt (prefixEnergy_nonneg _ _),mul_pow] using hs
  have hbound (K : ℕ) : prefixEnergy (fun k => f^[k] z₀) K ≤ M*‖z₀‖^2 := by
    have := henergy K
    dsimp [M]
    nlinarith [sq_nonneg ‖z₀‖]
  exact ⟨finiteEnergy_of_prefix_bound _ _ (by positivity) hbound,
    energy_le_of_prefix_bound _ _ (by positivity) hbound⟩

end
end Populus.ModelReduction.Certified
