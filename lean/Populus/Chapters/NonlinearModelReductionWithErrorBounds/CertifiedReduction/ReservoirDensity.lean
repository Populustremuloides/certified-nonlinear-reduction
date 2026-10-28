import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.MatrixNormBounds
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.SmoothNormalizationDensity
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.VectorBlocks

/-!
# Paper-facing prescribed-envelope reservoir density

Correspondence: Appendix A.3, `prop:reservoir`. `Ω` uses Fin concatenation,
which is the standard-coordinate version of the earlier Sum-indexed norm
identity. The driving norm stays exactly `‖w(v)‖`; it is never a lifted-input
norm. Approximation is of `B_δ e`, with the injection fixed throughout.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
variable {b d p q : ℕ}

def Ω (w : Rn d) (h : Rn p) : Rn (p+d) :=
  (Real.sqrt (1+‖h‖^2))⁻¹ • join (‖w‖ • h) w

/-- Exact global norm preservation for every finite network coefficient. -/
theorem norm_Ω_eq (w : Rn d) (h : Rn p) : ‖Ω w h‖=‖w‖ := by
  let D : ℝ := Real.sqrt (1+‖h‖^2)
  have hD : 0<D := by dsimp [D]; positivity
  have hD2 : D^2=1+‖h‖^2 := Real.sq_sqrt (by positivity)
  have hs := norm_join_sq (‖w‖ • h) w
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg w)] at hs
  have hn : ‖join (‖w‖ • h) w‖=‖w‖*D := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hD.le)).1
    nlinarith
  change ‖D⁻¹ • join (‖w‖ • h) w‖=‖w‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hD),hn]
  field_simp

/-- The extended reservoir injection is exactly the smooth-envelope residual. -/
theorem reservoir_injection (B_δ : Mat q p) (w : Rn d) (h : Rn p) :
    act (zeroExtension B_δ d) (Ω w h)=act B_δ (‖w‖ • ν h) := by
  rw [act_zeroExtension]
  congr 1
  simp only [Ω,take_smul,take_join,ν,smul_smul]
  congr 1
  ring

/-- **Paper Proposition `prop:reservoir`: Prescribed-envelope reservoir density.**

For every tolerance the actual extended-injection residual approximates
`B_δ e` uniformly. In addition to the printed density and Gram/gain equality,
the conclusion retains the global norm-preservation identity for this same
finite coefficient network. No rank premise is imposed on `B_δ`.
-/
theorem prescribed_envelope_reservoir_density
    (K : Set (Rn b)) (hK : IsCompact K) (hKne : K.Nonempty)
    (w : Rn b → Rn d) (hw : Continuous w)
    (e : C(K,Rn p)) (he : ∀ v : K, ‖e v‖≤‖w v‖)
    (B_δ : Mat q p) (ε : ℝ) (hε : 0<ε) :
    (∃ N : ReLUNetwork b p,
      sSup (Set.range (fun v : K => ‖act B_δ (e v)-act (zeroExtension B_δ d) (Ω (w v) (N.eval v))‖))<ε ∧
      (∀ v : Rn b, ‖Ω (w v) (N.eval v)‖=‖w v‖)) ∧
    zeroExtension B_δ d*(zeroExtension B_δ d).transpose=B_δ*B_δ.transpose ∧
    (∀ (A : Mat q q) (o : ℕ) (O : Mat o q),
      channelGain A (zeroExtension B_δ d) O=channelGain A B_δ O) := by
  refine ⟨?_,zeroExtension_gram B_δ d,fun A o O => zeroExtension_channel_gain A B_δ O d⟩
  let δ : ℝ := ε/(2*(1+‖B_δ‖))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨N,hN,_⟩ := smooth_fixed_envelope_pointwise_approximation K hK hKne
    (fun v => ‖w v‖) hw.norm (fun v => norm_nonneg _) e he δ hδ
  have hδeq : δ*(2*(1+‖B_δ‖))=ε := div_mul_cancel₀ _ (by positivity : 2*(1+‖B_δ‖)≠0)
  have hsmall : ‖B_δ‖*δ<ε := by nlinarith [norm_nonneg B_δ]
  letI : Nonempty K := hKne.to_subtype
  refine ⟨N,lt_of_le_of_lt ?_ hsmall,fun v => norm_Ω_eq _ _⟩
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨v,rfl⟩
  dsimp only
  rw [reservoir_injection B_δ (w v) (N.eval v)]
  have heq : act B_δ (e v)-act B_δ (‖w v‖ • ν (N.eval v))=
      act B_δ (e v-‖w v‖ • ν (N.eval v)) := (map_sub (Matrix.toEuclideanLin B_δ) _ _).symm
  rw [heq]
  have hB : ‖act B_δ (e v-‖w v‖ • ν (N.eval v))‖ ≤
      ‖B_δ‖*‖e v-‖w v‖ • ν (N.eval v)‖ := norm_act_le B_δ _
  exact hB.trans (mul_le_mul_of_nonneg_left (hN v).le (norm_nonneg B_δ))

end
end Populus.ModelReduction.Certified
