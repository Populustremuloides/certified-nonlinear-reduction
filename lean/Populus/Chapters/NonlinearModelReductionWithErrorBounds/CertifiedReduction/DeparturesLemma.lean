import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.NonlinearDepartures

/-!
# Paper-facing nonlinear departures and stability lemma

Correspondence: Appendix C, `lem:departures`. All six gains below are the
actual induced gains of Definitions 5–6. Their conversion to reals is used
only under Schur hypotheses; `exact_channel_gain_prefix` proves finiteness.
`O = I` gives the full state and `O = V_r` the reconstructed reduced state.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {d q m p p_u p_z r : ℕ}

def g_u (N : NominalMatrices d m p p_u p_z) (O : Mat q d) : ℝ :=
  (channelGain N.A N.B_u O).toReal
def g_δu (N : NominalMatrices d m p p_u p_z) (O : Mat q d) : ℝ :=
  (channelGain N.A N.B_δu O).toReal
def g_δz (N : NominalMatrices d m p p_u p_z) (O : Mat q d) : ℝ :=
  (channelGain N.A N.B_δz O).toReal
def h_u (N : NominalMatrices d m p p_u p_z) : ℝ :=
  (channelGain N.A N.B_u N.C).toReal
def h_δu (N : NominalMatrices d m p p_u p_z) : ℝ :=
  (channelGain N.A N.B_δu N.C).toReal
def h_δz (N : NominalMatrices d m p p_u p_z) : ℝ :=
  (channelGain N.A N.B_δz N.C).toReal

def Γ (N : NominalMatrices d m p p_u p_z) (O : Mat q d) : ℝ :=
  (g_u N O+g_δu N O)/(1-g_δz N O)
def ε (N : NominalMatrices d m p p_u p_z) (O : Mat q d) : ℝ :=
  h_δz N*Γ N O+h_δu N

/-- Expanded conclusions for one of the two actual feedback recurrences.
This is a predicate containing the paper's estimates and stability claims,
not a bundle of assumptions or an opaque certificate interface. -/
def NonlinearDeparturesAndStability
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u) : Prop :=
  (∀ u, FiniteEnergy u →
    ℓ₂ (fun k => act O (rollout (drivenUpdate N O Δ_z Δ_u) 0 u k)) ≤
      ENNReal.ofReal (Γ N O)*ℓ₂ u) ∧
  inducedGain (departureResponse N O Δ_z Δ_u) ≤ ENNReal.ofReal (ε N O) ∧
  GloballyExponentiallyStable (fun z => drivenUpdate N O Δ_z Δ_u z 0) ∧
  inducedGain (nonlinearResponse N O Δ_z Δ_u) ≤ ENNReal.ofReal (h_u N+ε N O) ∧
  inducedGain (nonlinearResponse N O Δ_z Δ_u) ≠ ⊤ ∧
  (∀ u, FiniteEnergy u → FiniteEnergy (nonlinearResponse N O Δ_z Δ_u u))

/-- All conclusions of the paper's lemma for an injectively reconstructed
feedback loop. The strict margin concerns the actual nominal channel gain. -/
theorem nonlinear_departures_and_stability_for_loop [NeZero d]
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (hA : Schur N.A) (hO : Function.Injective (act O))
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖)
    (hsmall : g_δz N O<1) : NonlinearDeparturesAndStability N O Δ_z Δ_u := by
  have hgu := exact_channel_gain_prefix N.A N.B_u O hA
  have hgdu := exact_channel_gain_prefix N.A N.B_δu O hA
  have hgdz := exact_channel_gain_prefix N.A N.B_δz O hA
  have hhu := exact_channel_gain_prefix N.A N.B_u N.C hA
  have hhdu := exact_channel_gain_prefix N.A N.B_δu N.C hA
  have hhdz := exact_channel_gain_prefix N.A N.B_δz N.C hA
  have hΓ : 0 ≤ Γ N O := div_nonneg (add_nonneg hgu.1 hgdu.1) (by change 0≤1-g_δz N O; linarith)
  have hε : 0 ≤ ε N O := add_nonneg (mul_nonneg hhdz.1 hΓ) hhdu.1
  have hdep : inducedGain (departureResponse N O Δ_z Δ_u) ≤ ENNReal.ofReal (ε N O) :=
    nonlinear_departure_gain_bound N O Δ_z Δ_u hz hu (g_u N O) (g_δu N O) (g_δz N O)
      (h_δu N) (h_δz N) hgu hgdu hgdz hhdu hhdz hsmall
  have hgain := nonlinear_zero_state_gain_bound N O Δ_z Δ_u hz hu (h_u N) (ε N O) hε hhu hdep
  refine ⟨?_,hdep,feedback_globally_exponentially_stable N O hA hO Δ_z Δ_u hz hu
    (g_δz N O) hgdz hsmall,hgain,ne_of_lt (hgain.trans_lt ENNReal.ofReal_lt_top),?_⟩
  · intro u _
    exact ℓ₂_le_of_prefix_bound _ _ (Γ N O) hΓ
      (observed_state_prefix_bound N O Δ_z Δ_u hz hu (g_u N O) (g_δu N O) (g_δz N O)
        hgu hgdu hgdz hsmall u)
  · intro u hu'
    exact finiteEnergy_of_gain_bound _ u hu' (h_u N+ε N O)
      ((inducedGain_le_iff _ (nonlinearResponse_zero N O Δ_z Δ_u hz hu) _
        (add_nonneg hhu.1 hε)).1 hgain u hu')

/-- `W_r V_r = I` implies the injectivity needed to recover reduced-state
energy from reconstructed-state energy. -/
theorem reconstruction_injective_of_left_inverse (W_r : Mat r q) (V_r : Mat q r)
    (hWV : W_r*V_r=1) : Function.Injective (act V_r) := by
  intro x y h
  have hW := congrArg (act W_r) h
  simpa only [← act_mul,hWV,act_one] using hW

/-- **Paper Lemma `lem:departures`: Nonlinear departures and stability.**

The two actual recurrences are the full predictor and its projected reduction,
with state observations `I` and `V_r`. The predicate expands to both printed
state-gain and output-departure inequalities, autonomous global exponential
stability, and finite individual zero-state gains. Standing `W_r V_r = I`
is used only to derive injectivity; the following corollary removes it. -/
theorem nonlinear_departures_and_stability [NeZero q] [NeZero r]
    (N : NominalMatrices q m p p_u p_z) (W_r : Mat r q) (V_r : Mat q r)
    (hWV : W_r*V_r=1) (hA : Schur N.A) (hA_hat : Schur (N.reduced W_r V_r).A)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖)
    (hsmall : g_δz N (1 : Mat q q)<1) (hsmall_hat : g_δz (N.reduced W_r V_r) V_r<1) :
    NonlinearDeparturesAndStability N (1 : Mat q q) Δ_z Δ_u ∧
    NonlinearDeparturesAndStability (N.reduced W_r V_r) V_r Δ_z Δ_u := by
  exact ⟨nonlinear_departures_and_stability_for_loop N (1 : Mat q q) hA (by intro x y h; simpa using h)
      Δ_z Δ_u hz hu hsmall,
    nonlinear_departures_and_stability_for_loop (N.reduced W_r V_r) V_r hA_hat
      (reconstruction_injective_of_left_inverse W_r V_r hWV) Δ_z Δ_u hz hu hsmall_hat⟩

end
end Populus.ModelReduction.Certified
