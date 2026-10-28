import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.DeparturesLemma

/-!
# Certified channel-gain uppers used by the computable certificate

Definition `def:constructed-certificate` uses finite certified upper bounds,
not necessarily the exact gains. This module keeps the six chosen real upper
bounds and their validity separate. Matrix-storage witnesses will discharge
validity; no nonlinear stability or error conclusion is an assumed field.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {d q m p p_u p_z : ℕ}

structure GainBounds where
  g_u : ℝ
  g_δu : ℝ
  g_δz : ℝ
  h_u : ℝ
  h_δu : ℝ
  h_δz : ℝ

namespace GainBounds

def Valid (G : GainBounds) (N : NominalMatrices d m p p_u p_z) (O : Mat q d) : Prop :=
  HasPrefixChannelGain N.A N.B_u O G.g_u ∧
  HasPrefixChannelGain N.A N.B_δu O G.g_δu ∧
  HasPrefixChannelGain N.A N.B_δz O G.g_δz ∧
  HasPrefixChannelGain N.A N.B_u N.C G.h_u ∧
  HasPrefixChannelGain N.A N.B_δu N.C G.h_δu ∧
  HasPrefixChannelGain N.A N.B_δz N.C G.h_δz ∧ G.g_δz<1

def Γ (G : GainBounds) : ℝ := (G.g_u+G.g_δu)/(1-G.g_δz)
def ε (G : GainBounds) : ℝ := G.h_δz*G.Γ+G.h_δu

theorem Γ_nonneg (G : GainBounds) (h : G.Valid N O) : 0 ≤ G.Γ :=
  div_nonneg (add_nonneg h.1.1 h.2.1.1) (by have := h.2.2.2.2.2.2; linarith)

theorem ε_nonneg (G : GainBounds) (h : G.Valid N O) : 0 ≤ G.ε :=
  add_nonneg (mul_nonneg h.2.2.2.2.2.1.1 (G.Γ_nonneg h)) h.2.2.2.2.1.1

theorem h_u_nonneg (G : GainBounds) (h : G.Valid N O) : 0 ≤ G.h_u := h.2.2.2.1.1

/-- Exact nominal gains provide one instance of valid upper bounds when the
strict margin holds. Certified storage uppers provide other instances. -/
def exact (N : NominalMatrices d m p p_u p_z) (O : Mat q d) : GainBounds where
  g_u := Certified.g_u N O
  g_δu := Certified.g_δu N O
  g_δz := Certified.g_δz N O
  h_u := Certified.h_u N
  h_δu := Certified.h_δu N
  h_δz := Certified.h_δz N

theorem exact_valid [NeZero d] (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (hA : Schur N.A) (hsmall : Certified.g_δz N O<1) : (exact N O).Valid N O :=
  ⟨exact_channel_gain_prefix N.A N.B_u O hA,
   exact_channel_gain_prefix N.A N.B_δu O hA,
   exact_channel_gain_prefix N.A N.B_δz O hA,
   exact_channel_gain_prefix N.A N.B_u N.C hA,
   exact_channel_gain_prefix N.A N.B_δu N.C hA,
   exact_channel_gain_prefix N.A N.B_δz N.C hA,hsmall⟩

/-- State, departure, autonomous-stability, and individual-gain conclusions
using the chosen certified upper bounds consistently in every term. -/
theorem conclusions [NeZero d]
    (G : GainBounds) (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (hG : G.Valid N O) (hA : Schur N.A) (hO : Function.Injective (act O))
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖) :
    (∀ u, FiniteEnergy u →
      ℓ₂ (fun k => act O (rollout (drivenUpdate N O Δ_z Δ_u) 0 u k)) ≤
        ENNReal.ofReal G.Γ*ℓ₂ u) ∧
    inducedGain (departureResponse N O Δ_z Δ_u) ≤ ENNReal.ofReal G.ε ∧
    GloballyExponentiallyStable (fun z => drivenUpdate N O Δ_z Δ_u z 0) ∧
    inducedGain (nonlinearResponse N O Δ_z Δ_u) ≤ ENNReal.ofReal (G.h_u+G.ε) := by
  rcases hG with ⟨hgu,hgdu,hgdz,hhu,hhdu,hhdz,hsmall⟩
  have hdep : inducedGain (departureResponse N O Δ_z Δ_u) ≤ ENNReal.ofReal G.ε :=
    nonlinear_departure_gain_bound N O Δ_z Δ_u hz hu G.g_u G.g_δu G.g_δz
      G.h_δu G.h_δz hgu hgdu hgdz hhdu hhdz hsmall
  refine ⟨?_,hdep,feedback_globally_exponentially_stable N O hA hO Δ_z Δ_u hz hu
    G.g_δz hgdz hsmall,nonlinear_zero_state_gain_bound N O Δ_z Δ_u hz hu G.h_u G.ε
      (G.ε_nonneg ⟨hgu,hgdu,hgdz,hhu,hhdu,hhdz,hsmall⟩) hhu hdep⟩
  intro u _
  exact ℓ₂_le_of_prefix_bound _ _ G.Γ (G.Γ_nonneg ⟨hgu,hgdu,hgdz,hhu,hhdu,hhdz,hsmall⟩)
    (observed_state_prefix_bound N O Δ_z Δ_u hz hu G.g_u G.g_δu G.g_δz hgu hgdu hgdz hsmall u)

end GainBounds
end
end Populus.ModelReduction.Certified
