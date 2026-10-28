import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.ReLUDensity
import Populus.PaperEvidence.ResidualEnvelope

/-!
# Uniform approximation under a fixed driving envelope

Paper result: `lem:fixed-envelope`, Appendix A. Coefficients are actual finite
ReLU computations from `ReLUDensity`; the target is continuous only on `K`.
The proof retains the envelope at every ambient input, including zeros of ρ.
-/

namespace Populus.ModelReduction.Certified
noncomputable section

abbrev rad {p : ℕ} (a : Rn p) := Populus.PaperEvidence.ModelReduction.rad a

/-- A direct norm estimate sufficient for approximation. In Euclidean spaces
the paper uses the sharper nonexpansive projection estimate; the factor two
here gives the identical arbitrary-tolerance conclusion. -/
theorem norm_rad_sub_le {p : ℕ} (a b : Rn p) (hb : ‖b‖ ≤ 1) :
    ‖rad a - b‖ ≤ 2 * ‖a-b‖ := by
  by_cases ha : ‖a‖ ≤ 1
  · simpa [rad, Populus.PaperEvidence.ModelReduction.rad, max_eq_left ha] using
      (show ‖a-b‖ ≤ 2 * ‖a-b‖ by nlinarith [norm_nonneg (a-b)])
  · have hap : 0 < ‖a‖ := by linarith
    have hi : ‖a‖⁻¹ ≤ 1 := (inv_le_one₀ hap).mpr (by linarith)
    have heq : rad a-a = (‖a‖⁻¹-1) • a := by
      simp only [rad, Populus.PaperEvidence.ModelReduction.rad, max_eq_right (by linarith : 1 ≤ ‖a‖)]
      module
    have hdist : ‖rad a-a‖ = ‖a‖-1 := by
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      field_simp
      <;> ring
    have hab : ‖a‖-1 ≤ ‖a-b‖ := by
      have htri : ‖a‖ ≤ ‖a-b‖ + ‖b‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub a b 0
      linarith
    calc
      ‖rad a-b‖ ≤ ‖rad a-a‖+‖a-b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = (‖a‖-1)+‖a-b‖ := by rw [hdist]
      _ ≤ 2*‖a-b‖ := by linarith

/-- Paper Lemma 1 (`lem:fixed-envelope`). The output is a finite ReLU network;
no approximation theorem or desired error conclusion is a hypothesis. -/
theorem fixed_envelope_pointwise_approximation {b p : ℕ}
    (K : Set (Rn b)) (hK : IsCompact K) (hKne : K.Nonempty)
    (ρ : Rn b → ℝ) (hρ : Continuous ρ) (hρnonneg : ∀ v, 0 ≤ ρ v)
    (e : C(K, Rn p)) (he : ∀ v : K, ‖e v‖ ≤ ρ v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ hθ : ReLUNetwork b p,
      (∀ v : K, ‖e v - ρ v • rad (hθ.eval v)‖ < ε) ∧
      (∀ v : Rn b, ‖ρ v • rad (hθ.eval v)‖ ≤ ρ v) := by
  obtain ⟨vmax, hvmax, hmax⟩ := hK.exists_isMaxOn hKne hρ.continuousOn
  let R : ℝ := ρ vmax
  have hR : 0 ≤ R := hρnonneg vmax
  let η : ℝ := ε / 4
  let δ : ℝ := ε / (8 * (1+R))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let d : C(K, Rn p) :=
    ⟨fun v => (max (ρ v) η)⁻¹ • e v,
      (((hρ.comp continuous_subtype_val).max continuous_const).inv₀
        (fun v => ne_of_gt (lt_of_lt_of_le hη (le_max_right _ _)))).smul e.continuous⟩
  have hd (v : K) : ‖d v‖ ≤ 1 := by
    have hm : 0 < max (ρ v) η := lt_of_lt_of_le hη (le_max_right _ _)
    simp only [d, ContinuousMap.coe_mk, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hm)]
    calc
      (max (ρ v) η)⁻¹ * ‖e v‖ ≤ (max (ρ v) η)⁻¹ * max (ρ v) η :=
        mul_le_mul_of_nonneg_left ((he v).trans (le_max_left _ _)) (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hm)
  obtain ⟨hθ, hhθ⟩ := uniform_vector_relu_approximation_on_compact K hK d δ hδ
  refine ⟨hθ, ?_, ?_⟩
  · intro v
    have hρv : 0 ≤ ρ v := hρnonneg v
    have hRv : ρ v ≤ R := hmax v.property
    have hreg : ‖e v - ρ v • d v‖ ≤ η := by
      by_cases hv : η ≤ ρ v
      · have hp : ρ v ≠ 0 := ne_of_gt (hη.trans_le hv)
        have hid : ρ v • d v = e v := by
          simp only [d, ContinuousMap.coe_mk, max_eq_left hv, smul_smul]
          rw [mul_inv_cancel₀ hp, one_smul]
        simp [hid, hη.le]
      · have hv' : ρ v < η := lt_of_not_ge hv
        have hid : e v - ρ v • d v = (1-ρ v/η) • e v := by
          simp only [d, ContinuousMap.coe_mk, max_eq_right hv'.le]
          module
        rw [hid, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by have := (div_le_one hη).2 hv'.le; linarith)]
        calc
          (1-ρ v/η)*‖e v‖ ≤ (1-ρ v/η)*ρ v :=
            mul_le_mul_of_nonneg_left (he v) (by have := (div_le_one hη).2 hv'.le; linarith)
          _ ≤ ρ v := by nlinarith [div_nonneg hρv hη.le]
          _ ≤ η := hv'.le
    have hn : ‖rad (hθ.eval v)-d v‖ < 2*δ :=
      (norm_rad_sub_le (hθ.eval v) (d v) (hd v)).trans_lt
        (mul_lt_mul_of_pos_left (hhθ v) (by norm_num))
    have herr : ‖e v-ρ v • rad (hθ.eval v)‖ ≤ η+2*R*δ := by
      calc
        _ ≤ ‖e v-ρ v • d v‖+‖ρ v • d v-ρ v • rad (hθ.eval v)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ η+ρ v * ‖d v-rad (hθ.eval v)‖ := by
          rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρv]
          exact add_le_add hreg le_rfl
        _ ≤ η+R*(2*δ) := by
          gcongr
          simpa [norm_sub_rev] using hn.le
        _ = η+2*R*δ := by ring
    have hfinal : η+2*R*δ < ε := by
      dsimp [η,δ]
      field_simp
      nlinarith
    exact herr.trans_lt hfinal
  · intro v
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρnonneg v)]
    exact (mul_le_mul_of_nonneg_left
      (Populus.PaperEvidence.ModelReduction.norm_rad_le_one _) (hρnonneg v)).trans_eq (mul_one _)


/-- Paper Lemma 1 (`lem:fixed-envelope`), in the printed supremum form.
The subtype `v : K` represents the paper's target defined only on `K`.
The network is an actual finite affine/ReLU feedforward computation. -/
theorem uniform_approximation_with_fixed_driving_envelope {b p : ℕ}
    (K : Set (Rn b)) (hK : IsCompact K) (hKne : K.Nonempty)
    (ρ : Rn b → ℝ) (hρ : Continuous ρ) (hρnonneg : ∀ v, 0 ≤ ρ v)
    (e : C(K, Rn p)) (he : ∀ v : K, ‖e v‖ ≤ ρ v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ hθ : ReLUNetwork b p,
      sSup (Set.range (fun v : K => ‖e v - ρ v • rad (hθ.eval v)‖)) < ε ∧
      (∀ v : Rn b, ‖ρ v • rad (hθ.eval v)‖ ≤ ρ v) := by
  obtain ⟨hθ, happ, henv⟩ := fixed_envelope_pointwise_approximation
    K hK hKne ρ hρ hρnonneg e he (ε/2) (half_pos hε)
  letI : Nonempty K := hKne.to_subtype
  refine ⟨hθ, lt_of_le_of_lt ?_ (half_lt_self hε), henv⟩
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨v,rfl⟩
  exact (happ v).le

end
end Populus.ModelReduction.Certified
