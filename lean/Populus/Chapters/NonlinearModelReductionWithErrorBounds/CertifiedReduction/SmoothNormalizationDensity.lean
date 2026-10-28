import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.EnvelopeApproximation
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# ReLU density after the reservoir's smooth normalization

The paper uses `ν(h)=h/sqrt(1+‖h‖²)`. Mathlib's open-unit-ball homeomorphism
is exactly this map. Compact-open continuity of composition gives density
without assuming a derivative bound or an approximation theorem for ν-nets.
-/
namespace Populus.ModelReduction.Certified
noncomputable section
variable {b p : ℕ}

def ν (h : Rn p) : Rn p := (Real.sqrt (1+‖h‖^2))⁻¹ • h

theorem continuous_ν : Continuous (ν : Rn p → Rn p) := by
  have hi : Continuous (fun h : Rn p => (Real.sqrt (1+‖h‖^2))⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun h => Real.sqrt_ne_zero'.mpr (by positivity))
  exact hi.smul continuous_id

theorem ν_eq_unitBall (h : Rn p) : ν h=(Homeomorph.unitBall h : Rn p) := by rfl

theorem norm_ν_lt_one (h : Rn p) : ‖ν h‖<1 := by
  rw [ν_eq_unitBall]
  exact mem_ball_zero_iff.1 (Homeomorph.unitBall h).property

/-- Postcomposition by any continuous map preserves uniform approximation
of a compact-domain coefficient target by actual finite ReLU networks. -/
theorem uniform_post_relu_approximation
    (K : Set (Rn b)) (hK : IsCompact K) (h : C(K,Rn p))
    (f : C(Rn p,Rn p)) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ReLUNetwork b p, ∀ v : K, ‖f (N.eval v)-f (h v)‖<ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun g : C(K,Rn p) => f.comp g) := f.continuous_postcomp
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.1 hc.continuousAt ε hε
  obtain ⟨N,hN⟩ := uniform_vector_relu_approximation_on_compact K hK h δ hδ
  have hNeval : Continuous N.eval :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (N i).continuous_eval))
  let N_K : C(K,Rn p) := ⟨fun v => N.eval v,hNeval.comp continuous_subtype_val⟩
  have hnorm : ‖N_K-h‖<δ := (ContinuousMap.norm_lt_iff _ hδ).2 hN
  have hdist : dist (f.comp N_K) (f.comp h)<ε := hclose (by simpa only [dist_eq_norm] using hnorm)
  have hp := (ContinuousMap.norm_lt_iff _ hε).1 (by simpa only [dist_eq_norm] using hdist)
  exact ⟨N,fun v => hp v⟩

/-- Any continuous coefficient taking values strictly inside the unit ball
can be approximated after smooth normalization of a finite ReLU network. -/
theorem uniform_ν_relu_approximation_open_ball
    (K : Set (Rn b)) (hK : IsCompact K) (d : C(K,Rn p))
    (hd : ∀ v, ‖d v‖<1) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ReLUNetwork b p, ∀ v : K, ‖ν (N.eval v)-d v‖<ε := by
  let db : C(K,Metric.ball (0 : Rn p) 1) :=
    ⟨fun v => ⟨d v,mem_ball_zero_iff.2 (hd v)⟩,
      d.continuous.subtype_mk (fun v => mem_ball_zero_iff.2 (hd v))⟩
  let H : Rn p ≃ₜ Metric.ball (0 : Rn p) 1 := Homeomorph.unitBall
  let h : C(K,Rn p) := (⟨H.symm,H.symm.continuous⟩ : C(Metric.ball (0 : Rn p) 1,Rn p)).comp db
  obtain ⟨N,hN⟩ := uniform_post_relu_approximation K hK h ⟨ν,continuous_ν⟩ ε hε
  refine ⟨N,fun v => ?_⟩
  have heq : ν (h v)=d v := by
    rw [ν_eq_unitBall]
    exact congrArg Subtype.val (H.apply_symm_apply (db v))
  simpa only [ContinuousMap.coe_mk,heq] using hN v

/-- Approximation extends to the closed unit ball by first shrinking its
continuous target slightly toward the origin. -/
theorem uniform_ν_relu_approximation_closed_ball
    (K : Set (Rn b)) (hK : IsCompact K) (d : C(K,Rn p))
    (hd : ∀ v, ‖d v‖≤1) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ReLUNetwork b p, ∀ v : K, ‖ν (N.eval v)-d v‖<ε := by
  let η : ℝ := min (1/2) (ε/4)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1/2 := min_le_left _ _
  have hηε : η≤ε/4 := min_le_right _ _
  let dη : C(K,Rn p) := (1-η) • d
  have hdη (v : K) : ‖dη v‖<1 := by
    have heq : ‖dη v‖=(1-η)*‖d v‖ := by
      simp only [dη,ContinuousMap.smul_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0≤1-η)]
    rw [heq]
    have := mul_le_mul_of_nonneg_left (hd v) (by linarith : 0≤1-η)
    nlinarith
  obtain ⟨N,hN⟩ := uniform_ν_relu_approximation_open_ball K hK dη hdη (ε/2) (by positivity)
  refine ⟨N,fun v => ?_⟩
  have hshrink : ‖dη v-d v‖≤η := by
    have heq : dη v-d v=(-η) • d v := by dsimp [dη]; module
    rw [heq,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hη]
    exact (mul_le_mul_of_nonneg_left (hd v) hη.le).trans (by simp)
  have ht := norm_sub_le_norm_sub_add_norm_sub (ν (N.eval v)) (dη v) (d v)
  linarith [hN v]

theorem continuous_rad : Continuous (rad : Rn p → Rn p) := by
  apply Continuous.smul _ continuous_id
  exact Continuous.inv₀ (continuous_const.max continuous_norm)
    (fun v => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖v‖)))

/-- Smooth normalized coefficients uniformly approximate every continuous
residual obeying the fixed driving envelope, including envelope zeros. -/
theorem smooth_fixed_envelope_pointwise_approximation
    (K : Set (Rn b)) (hK : IsCompact K) (hKne : K.Nonempty)
    (ρ : Rn b → ℝ) (hρ : Continuous ρ) (hρnonneg : ∀ v, 0≤ρ v)
    (e : C(K,Rn p)) (he : ∀ v : K, ‖e v‖≤ρ v) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ReLUNetwork b p,
      (∀ v : K, ‖e v-ρ v • ν (N.eval v)‖<ε) ∧
      (∀ v : Rn b, ‖ρ v • ν (N.eval v)‖≤ρ v) := by
  obtain ⟨vmax,hvmax,hmax⟩ := hK.exists_isMaxOn hKne hρ.continuousOn
  let R : ℝ := ρ vmax
  have hR : 0≤R := hρnonneg vmax
  obtain ⟨M,hM,_⟩ := fixed_envelope_pointwise_approximation K hK hKne ρ hρ hρnonneg e he
    (ε/2) (by positivity)
  have hMeval : Continuous M.eval :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (M i).continuous_eval))
  let d : C(K,Rn p) := ⟨fun v => rad (M.eval v),
    continuous_rad.comp (hMeval.comp continuous_subtype_val)⟩
  have hd (v : K) : ‖d v‖≤1 := Populus.PaperEvidence.ModelReduction.norm_rad_le_one _
  let δ : ℝ := ε/(2*(1+R))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨N,hN⟩ := uniform_ν_relu_approximation_closed_ball K hK d hd δ hδ
  refine ⟨N,?_,?_⟩
  · intro v
    have hρv := hρnonneg v
    have hRv : ρ v≤R := hmax v.property
    have hδeq : δ*(2*(1+R))=ε := div_mul_cancel₀ _ (by positivity : 2*(1+R)≠0)
    have hscaled : ‖ρ v • d v-ρ v • ν (N.eval v)‖≤R*δ := by
      rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hρv]
      have hn : ‖d v-ν (N.eval v)‖≤δ := by simpa only [norm_sub_rev] using (hN v).le
      exact mul_le_mul hRv hn (norm_nonneg _) hR
    have ht := norm_sub_le_norm_sub_add_norm_sub (e v) (ρ v • d v) (ρ v • ν (N.eval v))
    have hm : ‖e v-ρ v • d v‖<ε/2 := hM v
    nlinarith
  · intro v
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hρnonneg v)]
    exact (mul_le_mul_of_nonneg_left (norm_ν_lt_one _).le (hρnonneg v)).trans (by simp)

end
end Populus.ModelReduction.Certified
