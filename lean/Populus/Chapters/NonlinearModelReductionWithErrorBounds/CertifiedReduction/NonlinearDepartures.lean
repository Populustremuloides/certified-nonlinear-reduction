import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.FeedbackStability
import Populus.Chapters.NonlinearModelReductionWithErrorBounds.CertifiedReduction.OperatorGains

/-!
# Nonlinear output departures and finite zero-state input–output gains

Paper: `eq:penalties` and `lem:departures`. Every response below is computed
from the actual recurrence; residual signals are not independent placeholders.
-/
namespace Populus.ModelReduction.Certified
open scoped ENNReal
noncomputable section
variable {d q m p p_u p_z : ℕ}

def nonlinearResponse (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (u : ℕ → Rn m) (k : ℕ) : Rn p :=
  act N.C (rollout (drivenUpdate N O Δ_z Δ_u) 0 u k)

def nominalResponse (N : NominalMatrices d m p p_u p_z)
    (u : ℕ → Rn m) (k : ℕ) : Rn p := act N.C (linearResponse N.A N.B_u u k)

def departureResponse (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (u : ℕ → Rn m) (k : ℕ) : Rn p :=
  nonlinearResponse N O Δ_z Δ_u u k-nominalResponse N u k

@[simp] theorem nonlinearResponse_zero
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖) :
    nonlinearResponse N O Δ_z Δ_u (fun _ => 0)=fun _ => 0 := by
  have hz0 : Δ_z 0=0 := norm_eq_zero.mp (le_antisymm (by simpa using hz 0) (norm_nonneg _))
  have hu0 : Δ_u 0 0=0 := norm_eq_zero.mp (le_antisymm (by simpa using hu 0 0) (norm_nonneg _))
  have hstate (k : ℕ) : rollout (drivenUpdate N O Δ_z Δ_u) 0 (fun _ => 0) k=0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [rollout,ih,drivenUpdate,hz0,hu0]
  funext k
  simp [nonlinearResponse,hstate]

@[simp] theorem nominalResponse_zero (N : NominalMatrices d m p p_u p_z) :
    nominalResponse N (fun _ => 0)=fun _ => 0 := by
  funext k
  simp [nominalResponse]

@[simp] theorem departureResponse_zero
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖) :
    departureResponse N O Δ_z Δ_u (fun _ => 0)=fun _ => 0 := by
  funext k
  simp only [departureResponse,nonlinearResponse_zero N O Δ_z Δ_u hz hu,nominalResponse_zero,sub_self]

theorem departure_decomposition
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (u : ℕ → Rn m) (k : ℕ) :
    let z := rollout (drivenUpdate N O Δ_z Δ_u) 0 u
    departureResponse N O Δ_z Δ_u u k=
      act N.C (linearResponse N.A N.B_δu (fun j => Δ_u (act O (z j)) (u j)) k)+
      act N.C (linearResponse N.A N.B_δz (fun j => Δ_z (act O (z j))) k) := by
  dsimp only [departureResponse,nonlinearResponse,nominalResponse]
  rw [trajectory_decomposition N O Δ_z Δ_u 0 u k]
  simp only [freeResponse_zero,zero_add,act_add]
  abel

/-- The paper's `Γ` estimate, valid on every finite prefix without assuming
finite input or state energy. -/
theorem observed_state_prefix_bound
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖)
    (g_u g_δu g_δz : ℝ)
    (hg_u : HasPrefixChannelGain N.A N.B_u O g_u)
    (hg_δu : HasPrefixChannelGain N.A N.B_δu O g_δu)
    (hg_δz : HasPrefixChannelGain N.A N.B_δz O g_δz)
    (hsmall : g_δz<1) (u : ℕ → Rn m) (K : ℕ) :
    prefixNorm (fun k => act O (rollout (drivenUpdate N O Δ_z Δ_u) 0 u k)) K ≤
      ((g_u+g_δu)/(1-g_δz))*prefixNorm u K := by
  have hp := observed_state_prefix_estimate N O Δ_z Δ_u hz hu g_u g_δu g_δz
    hg_u hg_δu hg_δz u K
  rw [div_mul_eq_mul_div,le_div_iff₀ (by linarith : 0<1-g_δz)]
  nlinarith

/-- The two actual residual-driven output channels give the printed departure
constant `ε = h_δz Γ + h_δu`. -/
theorem departure_prefix_bound
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖)
    (g_u g_δu g_δz h_δu h_δz : ℝ)
    (hg_u : HasPrefixChannelGain N.A N.B_u O g_u)
    (hg_δu : HasPrefixChannelGain N.A N.B_δu O g_δu)
    (hg_δz : HasPrefixChannelGain N.A N.B_δz O g_δz)
    (hh_δu : HasPrefixChannelGain N.A N.B_δu N.C h_δu)
    (hh_δz : HasPrefixChannelGain N.A N.B_δz N.C h_δz)
    (hsmall : g_δz<1) (u : ℕ → Rn m) (K : ℕ) :
    prefixNorm (departureResponse N O Δ_z Δ_u u) K ≤
      (h_δz*((g_u+g_δu)/(1-g_δz))+h_δu)*prefixNorm u K := by
  let z := rollout (drivenUpdate N O Δ_z Δ_u) 0 u
  let δ_u := fun k => Δ_u (act O (z k)) (u k)
  let δ_z := fun k => Δ_z (act O (z k))
  have hdu : prefixNorm δ_u K ≤ prefixNorm u K := prefixNorm_mono _ _ (fun k => hu _ _) K
  have hdz : prefixNorm δ_z K ≤ ((g_u+g_δu)/(1-g_δz))*prefixNorm u K :=
    (prefixNorm_mono _ _ (fun k => hz _) K).trans
      (observed_state_prefix_bound N O Δ_z Δ_u hz hu g_u g_δu g_δz hg_u hg_δu hg_δz hsmall u K)
  have hdecomp : departureResponse N O Δ_z Δ_u u=fun k =>
      act N.C (linearResponse N.A N.B_δu δ_u k)+act N.C (linearResponse N.A N.B_δz δ_z k) := by
    funext k
    exact departure_decomposition N O Δ_z Δ_u u k
  calc
    _ = prefixNorm (fun k => act N.C (linearResponse N.A N.B_δu δ_u k)+
          act N.C (linearResponse N.A N.B_δz δ_z k)) K := congrArg (fun s => prefixNorm s K) hdecomp
    _ ≤ _ := prefixNorm_add_le _ _ K
    _ ≤ h_δu*prefixNorm δ_u K+h_δz*prefixNorm δ_z K :=
      add_le_add (hh_δu.2 δ_u K) (hh_δz.2 δ_z K)
    _ ≤ h_δu*prefixNorm u K+h_δz*(((g_u+g_δu)/(1-g_δz))*prefixNorm u K) :=
      add_le_add (mul_le_mul_of_nonneg_left hdu hh_δu.1) (mul_le_mul_of_nonneg_left hdz hh_δz.1)
    _ = _ := by ring

/-- The actual nonlinear/nominal output difference has the paper's induced-
gain bound, over all finite-energy applied inputs. -/
theorem nonlinear_departure_gain_bound
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖)
    (g_u g_δu g_δz h_δu h_δz : ℝ)
    (hg_u : HasPrefixChannelGain N.A N.B_u O g_u)
    (hg_δu : HasPrefixChannelGain N.A N.B_δu O g_δu)
    (hg_δz : HasPrefixChannelGain N.A N.B_δz O g_δz)
    (hh_δu : HasPrefixChannelGain N.A N.B_δu N.C h_δu)
    (hh_δz : HasPrefixChannelGain N.A N.B_δz N.C h_δz)
    (hsmall : g_δz<1) :
    inducedGain (departureResponse N O Δ_z Δ_u) ≤
      ENNReal.ofReal (h_δz*((g_u+g_δu)/(1-g_δz))+h_δu) := by
  have heps : 0 ≤ h_δz*((g_u+g_δu)/(1-g_δz))+h_δu :=
    add_nonneg (mul_nonneg hh_δz.1 (div_nonneg (add_nonneg hg_u.1 hg_δu.1)
      (by linarith))) hh_δu.1
  apply (inducedGain_le_iff _ (departureResponse_zero N O Δ_z Δ_u hz hu) _ heps).2
  intro u _
  exact ℓ₂_le_of_prefix_bound _ _ _ heps
    (departure_prefix_bound N O Δ_z Δ_u hz hu g_u g_δu g_δz h_δu h_δz
      hg_u hg_δu hg_δz hh_δu hh_δz hsmall u)

/-- Adding the nominal applied-input response gives a finite individual gain. -/
theorem nonlinear_zero_state_gain_bound
    (N : NominalMatrices d m p p_u p_z) (O : Mat q d)
    (Δ_z : Rn q → Rn p_z) (Δ_u : Rn q → Rn m → Rn p_u)
    (hz : ∀ z, ‖Δ_z z‖ ≤ ‖z‖) (hu : ∀ z u, ‖Δ_u z u‖ ≤ ‖u‖)
    (h_u ε : ℝ) (hε : 0 ≤ ε)
    (hh_u : HasPrefixChannelGain N.A N.B_u N.C h_u)
    (hdeparture : inducedGain (departureResponse N O Δ_z Δ_u) ≤ ENNReal.ofReal ε) :
    inducedGain (nonlinearResponse N O Δ_z Δ_u) ≤ ENNReal.ofReal (h_u+ε) := by
  have hnominal : inducedGain (nominalResponse N) ≤ ENNReal.ofReal h_u := by
    apply (inducedGain_le_iff _ (nominalResponse_zero N) _ hh_u.1).2
    exact (hasChannelGain_of_hasPrefixChannelGain N.A N.B_u N.C h_u hh_u).2
  have h := inducedGain_add_bound (nominalResponse N) (departureResponse N O Δ_z Δ_u)
    (nominalResponse_zero N) (departureResponse_zero N O Δ_z Δ_u hz hu)
    h_u ε hh_u.1 hε hnominal hdeparture
  have heq : (fun u k => nominalResponse N u k+departureResponse N O Δ_z Δ_u u k)=
      nonlinearResponse N O Δ_z Δ_u := by
    funext u k
    dsimp [departureResponse]
    abel
  rwa [heq] at h

end
end Populus.ModelReduction.Certified
