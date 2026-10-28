import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.GainWitnesses

/-!
# Uniform nonlinear reduction comparison

Paper: `prop:certificate`, Appendix D.1. Independent full and reduced residual
maps are allowed. All constants are the same chosen certified upper bounds
throughout; no cancellation, incremental estimate, or shared operator is used.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {q r m p p_u p_z : ℕ}

/-- Definition 3's conclusions, supplemented by the stronger exponential
stability proved in the text. `B` is an extended bound, including infinity. -/
def ReductionGuarantees
    (G G_hat : (ℕ → Rn m) → (ℕ → Rn p))
    (f : Rn q → Rn q) (f_hat : Rn r → Rn r) (B : ℝ≥0∞) : Prop :=
  GloballyExponentiallyStable f ∧ GloballyExponentiallyStable f_hat ∧
  GloballyAsymptoticallyStable f ∧ GloballyAsymptoticallyStable f_hat ∧
  inducedGain G≠⊤ ∧ inducedGain G_hat≠⊤ ∧
  inducedGain (fun u k => G u k-G_hat u k) ≤ B

/-- **Paper Proposition `prop:certificate`: Certified nonlinear state reduction.**

This is the uniform mathematical comparison underlying Definition 7. Its
premises are the chosen channel-gain witnesses, nominal-error witness and
feasible projection. The reduced update may use its own residual maps.
The separate matrix-witness adapter supplies the finite-matrix premises;
the invalid-witness branch of the extended certificate is handled separately.
-/
theorem uniform_nonlinear_comparison [NeZero q] [NeZero r]
    (N : NominalMatrices q m p p_u p_z) (W_r : Mat r q) (V_r : Mat q r)
    (hV : Function.Injective (act V_r))
    (hA : Schur N.A) (hA_hat : Schur (N.reduced W_r V_r).A)
    (G G_hat : GainBounds)
    (hG : G.Valid N (1 : Mat q q)) (hG_hat : G_hat.Valid (N.reduced W_r V_r) V_r)
    («b_r⁰» : ℝ) (hb : 0≤«b_r⁰»)
    (hnominal : inducedGain (fun u k => nominalResponse N u k-
      nominalResponse (N.reduced W_r V_r) u k) ≤ ENNReal.ofReal «b_r⁰»)
    («Δ_z¹» «Δ_z²» : Rn q → Rn p_z) («Δ_u¹» «Δ_u²» : Rn q → Rn m → Rn p_u)
    («hz¹» : ∀ z, ‖«Δ_z¹» z‖ ≤ ‖z‖) («hu¹» : ∀ z u, ‖«Δ_u¹» z u‖ ≤ ‖u‖)
    («hz²» : ∀ z, ‖«Δ_z²» z‖ ≤ ‖z‖) («hu²» : ∀ z u, ‖«Δ_u²» z u‖ ≤ ‖u‖) :
    ReductionGuarantees
      (nonlinearResponse N (1 : Mat q q) «Δ_z¹» «Δ_u¹»)
      (nonlinearResponse (N.reduced W_r V_r) V_r «Δ_z²» «Δ_u²»)
      (fun z => drivenUpdate N (1 : Mat q q) «Δ_z¹» «Δ_u¹» z 0)
      (fun z => drivenUpdate (N.reduced W_r V_r) V_r «Δ_z²» «Δ_u²» z 0)
      (ENNReal.ofReal (G.ε+«b_r⁰»+G_hat.ε)) := by
  have hfull := G.conclusions N (1 : Mat q q) hG hA (by intro x y h; simpa using h)
    «Δ_z¹» «Δ_u¹» «hz¹» «hu¹»
  have hred := G_hat.conclusions (N.reduced W_r V_r) V_r hG_hat hA_hat hV «Δ_z²» «Δ_u²» «hz²» «hu²»
  refine ⟨hfull.2.2.1,hred.2.2.1,hfull.2.2.1.gas,hred.2.2.1.gas,
    ne_of_lt (hfull.2.2.2.trans_lt ENNReal.ofReal_lt_top),
    ne_of_lt (hred.2.2.2.trans_lt ENNReal.ofReal_lt_top),?_⟩
  exact inducedGain_three_term_comparison
    (nonlinearResponse N (1 : Mat q q) «Δ_z¹» «Δ_u¹») (nominalResponse N)
    (nonlinearResponse (N.reduced W_r V_r) V_r «Δ_z²» «Δ_u²») (nominalResponse (N.reduced W_r V_r))
    (nonlinearResponse_zero N (1 : Mat q q) «Δ_z¹» «Δ_u¹» «hz¹» «hu¹») (nominalResponse_zero N)
    (nonlinearResponse_zero (N.reduced W_r V_r) V_r «Δ_z²» «Δ_u²» «hz²» «hu²»)
    (nominalResponse_zero (N.reduced W_r V_r))
    G.ε «b_r⁰» G_hat.ε (G.ε_nonneg hG) hb (G_hat.ε_nonneg hG_hat) hfull.2.1 hnominal hred.2.1

/-- With zero nominal applied-input injection both actual nominal responses
vanish, so the certified nominal error can be chosen to be exactly zero. -/
theorem nominalResponse_eq_zero_of_B_u_zero
    (N : NominalMatrices q m p p_u p_z) (hB : N.B_u=0) :
    nominalResponse N=fun _ _ => 0 := by
  funext u k
  have hstate (j : ℕ) : linearResponse N.A N.B_u u j=0 := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change act N.A (linearResponse N.A N.B_u u j)+act N.B_u (u j)=0
      rw [ih,hB,act_zero,zero_add]
      ext i
      simp [act,Matrix.toEuclideanLin]
  simp [nominalResponse,hstate]

/-- **Paper Corollary `cor:prescribed-projection`: Certification with a
prescribed reconstruction.** Here full column rank is expressed equivalently
as injectivity of the actual linear reconstruction. No `W_r V_r = I` premise
is present. The individual gain bounds are the printed ones; the zero-`B_u`
branch gives precisely the sum of the two nonlinear departure bounds. -/
theorem certification_with_prescribed_reconstruction [NeZero q] [NeZero r]
    (N : NominalMatrices q m p p_u p_z) (W_r : Mat r q) (V_r : Mat q r)
    (hV : Function.Injective (act V_r))
    (hA : Schur N.A) (hA_hat : Schur (N.reduced W_r V_r).A)
    (G G_hat : GainBounds)
    (hG : G.Valid N (1 : Mat q q)) (hG_hat : G_hat.Valid (N.reduced W_r V_r) V_r)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖) :
    GloballyExponentiallyStable (fun z => drivenUpdate N (1 : Mat q q) Δ_z Δ_u z 0) ∧
    GloballyExponentiallyStable (fun z => drivenUpdate (N.reduced W_r V_r) V_r Δ_z Δ_u z 0) ∧
    inducedGain (nonlinearResponse N (1 : Mat q q) Δ_z Δ_u) ≤ ENNReal.ofReal (G.h_u+G.ε) ∧
    inducedGain (nonlinearResponse (N.reduced W_r V_r) V_r Δ_z Δ_u) ≤
      ENNReal.ofReal (G_hat.h_u+G_hat.ε) ∧
    inducedGain (nonlinearResponse N (1 : Mat q q) Δ_z Δ_u)≠⊤ ∧
    inducedGain (nonlinearResponse (N.reduced W_r V_r) V_r Δ_z Δ_u)≠⊤ ∧
    (N.B_u=0 → inducedGain (fun u k => nonlinearResponse N (1 : Mat q q) Δ_z Δ_u u k-
      nonlinearResponse (N.reduced W_r V_r) V_r Δ_z Δ_u u k) ≤ ENNReal.ofReal (G.ε+G_hat.ε)) := by
  have hfull := G.conclusions N (1 : Mat q q) hG hA (by intro x y h; simpa using h) Δ_z Δ_u hz hu
  have hred := G_hat.conclusions (N.reduced W_r V_r) V_r hG_hat hA_hat hV Δ_z Δ_u hz hu
  refine ⟨hfull.2.2.1,hred.2.2.1,hfull.2.2.2,hred.2.2.2,
    ne_of_lt (hfull.2.2.2.trans_lt ENNReal.ofReal_lt_top),
    ne_of_lt (hred.2.2.2.trans_lt ENNReal.ofReal_lt_top),?_⟩
  intro hB
  have hB_hat : (N.reduced W_r V_r).B_u=0 := by simp [NominalMatrices.reduced,hB]
  have hnom : inducedGain (fun u k => nominalResponse N u k-
      nominalResponse (N.reduced W_r V_r) u k) ≤ ENNReal.ofReal 0 := by
    simp [nominalResponse_eq_zero_of_B_u_zero N hB,
      nominalResponse_eq_zero_of_B_u_zero (N.reduced W_r V_r) hB_hat,inducedGain]
  have h := uniform_nonlinear_comparison N W_r V_r hV hA hA_hat G G_hat hG hG_hat
    0 le_rfl hnom Δ_z Δ_z Δ_u Δ_u hz hu hz hu
  simpa only [add_zero] using h.2.2.2.2.2.2

end
end Populus.ModelReduction.Certified
